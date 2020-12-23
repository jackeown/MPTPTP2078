%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0765+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:52 EST 2020

% Result     : Theorem 26.86s
% Output     : CNFRefutation 26.86s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 140 expanded)
%              Number of clauses        :   29 (  34 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   20
%              Number of atoms          :  244 ( 649 expanded)
%              Number of equality atoms :   49 ( 117 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1142,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ~ ( ! [X1] :
              ~ ( ! [X2] :
                    ( r2_hidden(X2,k3_relat_1(X0))
                   => r2_hidden(k4_tarski(X1,X2),X0) )
                & r2_hidden(X1,k3_relat_1(X0)) )
          & k1_xboole_0 != k3_relat_1(X0)
          & v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1143,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ~ ( ! [X1] :
                ~ ( ! [X2] :
                      ( r2_hidden(X2,k3_relat_1(X0))
                     => r2_hidden(k4_tarski(X1,X2),X0) )
                  & r2_hidden(X1,k3_relat_1(X0)) )
            & k1_xboole_0 != k3_relat_1(X0)
            & v2_wellord1(X0) ) ) ),
    inference(negated_conjecture,[],[f1142])).

fof(f2262,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k1_xboole_0 != k3_relat_1(X0)
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1143])).

fof(f2263,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),X0)
              & r2_hidden(X2,k3_relat_1(X0)) )
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      & k1_xboole_0 != k3_relat_1(X0)
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f2262])).

fof(f3047,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X1,X2),X0)
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(X1,sK285(X1)),X0)
        & r2_hidden(sK285(X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3046,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
        & k1_xboole_0 != k3_relat_1(X0)
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ! [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k4_tarski(X1,X2),sK284)
              & r2_hidden(X2,k3_relat_1(sK284)) )
          | ~ r2_hidden(X1,k3_relat_1(sK284)) )
      & k1_xboole_0 != k3_relat_1(sK284)
      & v2_wellord1(sK284)
      & v1_relat_1(sK284) ) ),
    introduced(choice_axiom,[])).

fof(f3048,plain,
    ( ! [X1] :
        ( ( ~ r2_hidden(k4_tarski(X1,sK285(X1)),sK284)
          & r2_hidden(sK285(X1),k3_relat_1(sK284)) )
        | ~ r2_hidden(X1,k3_relat_1(sK284)) )
    & k1_xboole_0 != k3_relat_1(sK284)
    & v2_wellord1(sK284)
    & v1_relat_1(sK284) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK284,sK285])],[f2263,f3047,f3046])).

fof(f4997,plain,(
    ! [X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK285(X1)),sK284)
      | ~ r2_hidden(X1,k3_relat_1(sK284)) ) ),
    inference(cnf_transformation,[],[f3048])).

fof(f1147,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_wellord1(X1,X0)
       => ! [X2] :
            ~ ( ! [X3] :
                  ~ ( ! [X4] :
                        ( r2_hidden(X4,X2)
                       => r2_hidden(k4_tarski(X3,X4),X1) )
                    & r2_hidden(X3,X2) )
              & k1_xboole_0 != X2
              & r1_tarski(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2268,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1147])).

fof(f2269,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( r2_hidden(k4_tarski(X3,X4),X1)
                  | ~ r2_hidden(X4,X2) )
              & r2_hidden(X3,X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2268])).

fof(f3051,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X2) )
          & r2_hidden(X3,X2) )
     => ( ! [X4] :
            ( r2_hidden(k4_tarski(sK286(X1,X2),X4),X1)
            | ~ r2_hidden(X4,X2) )
        & r2_hidden(sK286(X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f3052,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ! [X4] :
                ( r2_hidden(k4_tarski(sK286(X1,X2),X4),X1)
                | ~ r2_hidden(X4,X2) )
            & r2_hidden(sK286(X1,X2),X2) )
          | k1_xboole_0 = X2
          | ~ r1_tarski(X2,X0) )
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK286])],[f2269,f3051])).

fof(f5004,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK286(X1,X2),X4),X1)
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3052])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3060,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5686,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK286(X1,X2),X4),X1)
      | ~ r2_hidden(X4,X2)
      | o_0_0_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f5004,f3060])).

fof(f1146,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2267,plain,(
    ! [X0] :
      ( ( r2_wellord1(X0,k3_relat_1(X0))
      <=> v2_wellord1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1146])).

fof(f3050,plain,(
    ! [X0] :
      ( ( ( r2_wellord1(X0,k3_relat_1(X0))
          | ~ v2_wellord1(X0) )
        & ( v2_wellord1(X0)
          | ~ r2_wellord1(X0,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2267])).

fof(f5002,plain,(
    ! [X0] :
      ( r2_wellord1(X0,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3050])).

fof(f4994,plain,(
    v2_wellord1(sK284) ),
    inference(cnf_transformation,[],[f3048])).

fof(f4993,plain,(
    v1_relat_1(sK284) ),
    inference(cnf_transformation,[],[f3048])).

fof(f4996,plain,(
    ! [X1] :
      ( r2_hidden(sK285(X1),k3_relat_1(sK284))
      | ~ r2_hidden(X1,k3_relat_1(sK284)) ) ),
    inference(cnf_transformation,[],[f3048])).

fof(f4995,plain,(
    k1_xboole_0 != k3_relat_1(sK284) ),
    inference(cnf_transformation,[],[f3048])).

fof(f5684,plain,(
    o_0_0_xboole_0 != k3_relat_1(sK284) ),
    inference(definition_unfolding,[],[f4995,f3060])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2348,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f2349,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2348])).

fof(f3119,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2349])).

fof(f5699,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f3119])).

fof(f5003,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK286(X1,X2),X2)
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f3052])).

fof(f5687,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK286(X1,X2),X2)
      | o_0_0_xboole_0 = X2
      | ~ r1_tarski(X2,X0)
      | ~ r2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f5003,f3060])).

cnf(c_1925,negated_conjecture,
    ( ~ r2_hidden(X0,k3_relat_1(sK284))
    | ~ r2_hidden(k4_tarski(X0,sK285(X0)),sK284) ),
    inference(cnf_transformation,[],[f4997])).

cnf(c_1935,plain,
    ( ~ r2_wellord1(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,X2)
    | r2_hidden(k4_tarski(sK286(X0,X2),X3),X0)
    | ~ v1_relat_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f5686])).

cnf(c_1933,plain,
    ( r2_wellord1(X0,k3_relat_1(X0))
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5002])).

cnf(c_21604,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k4_tarski(sK286(X3,X0),X2),X3)
    | ~ v2_wellord1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | X4 != X3
    | k3_relat_1(X4) != X1
    | o_0_0_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1935,c_1933])).

cnf(c_21605,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k4_tarski(sK286(X1,X0),X2),X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | o_0_0_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_21604])).

cnf(c_1928,negated_conjecture,
    ( v2_wellord1(sK284) ),
    inference(cnf_transformation,[],[f4994])).

cnf(c_21762,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k4_tarski(sK286(X1,X0),X2),X1)
    | ~ v1_relat_1(X1)
    | sK284 != X1
    | o_0_0_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21605,c_1928])).

cnf(c_21763,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK284))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(k4_tarski(sK286(sK284,X0),X1),sK284)
    | ~ v1_relat_1(sK284)
    | o_0_0_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_21762])).

cnf(c_1929,negated_conjecture,
    ( v1_relat_1(sK284) ),
    inference(cnf_transformation,[],[f4993])).

cnf(c_21765,plain,
    ( r2_hidden(k4_tarski(sK286(sK284,X0),X1),sK284)
    | ~ r2_hidden(X1,X0)
    | ~ r1_tarski(X0,k3_relat_1(sK284))
    | o_0_0_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21763,c_1929])).

cnf(c_21766,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK284))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(k4_tarski(sK286(sK284,X0),X1),sK284)
    | o_0_0_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_21765])).

cnf(c_104994,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK284))
    | ~ r2_hidden(sK286(sK284,X0),k3_relat_1(sK284))
    | ~ r2_hidden(sK285(sK286(sK284,X0)),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_1925,c_21766])).

cnf(c_1926,negated_conjecture,
    ( ~ r2_hidden(X0,k3_relat_1(sK284))
    | r2_hidden(sK285(X0),k3_relat_1(sK284)) ),
    inference(cnf_transformation,[],[f4996])).

cnf(c_105108,plain,
    ( ~ r1_tarski(k3_relat_1(sK284),k3_relat_1(sK284))
    | ~ r2_hidden(sK286(sK284,k3_relat_1(sK284)),k3_relat_1(sK284))
    | o_0_0_xboole_0 = k3_relat_1(sK284) ),
    inference(resolution,[status(thm)],[c_104994,c_1926])).

cnf(c_1927,negated_conjecture,
    ( o_0_0_xboole_0 != k3_relat_1(sK284) ),
    inference(cnf_transformation,[],[f5684])).

cnf(c_105123,plain,
    ( ~ r2_hidden(sK286(sK284,k3_relat_1(sK284)),k3_relat_1(sK284))
    | ~ r1_tarski(k3_relat_1(sK284),k3_relat_1(sK284)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_105108,c_1927])).

cnf(c_105124,plain,
    ( ~ r1_tarski(k3_relat_1(sK284),k3_relat_1(sK284))
    | ~ r2_hidden(sK286(sK284,k3_relat_1(sK284)),k3_relat_1(sK284)) ),
    inference(renaming,[status(thm)],[c_105123])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5699])).

cnf(c_105129,plain,
    ( ~ r2_hidden(sK286(sK284,k3_relat_1(sK284)),k3_relat_1(sK284)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_105124,c_69])).

cnf(c_1936,plain,
    ( ~ r2_wellord1(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r2_hidden(sK286(X0,X2),X2)
    | ~ v1_relat_1(X0)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f5687])).

cnf(c_21583,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK286(X2,X0),X0)
    | ~ v2_wellord1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | X3 != X2
    | k3_relat_1(X3) != X1
    | o_0_0_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1936,c_1933])).

cnf(c_21584,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r2_hidden(sK286(X1,X0),X0)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1)
    | o_0_0_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_21583])).

cnf(c_21782,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r2_hidden(sK286(X1,X0),X0)
    | ~ v1_relat_1(X1)
    | sK284 != X1
    | o_0_0_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21584,c_1928])).

cnf(c_21783,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK284))
    | r2_hidden(sK286(sK284,X0),X0)
    | ~ v1_relat_1(sK284)
    | o_0_0_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_21782])).

cnf(c_21787,plain,
    ( r2_hidden(sK286(sK284,X0),X0)
    | ~ r1_tarski(X0,k3_relat_1(sK284))
    | o_0_0_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21783,c_1929])).

cnf(c_21788,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK284))
    | r2_hidden(sK286(sK284,X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_21787])).

cnf(c_105174,plain,
    ( ~ r1_tarski(k3_relat_1(sK284),k3_relat_1(sK284))
    | o_0_0_xboole_0 = k3_relat_1(sK284) ),
    inference(resolution,[status(thm)],[c_105129,c_21788])).

cnf(c_105182,plain,
    ( ~ r1_tarski(k3_relat_1(sK284),k3_relat_1(sK284)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_105174,c_1927])).

cnf(c_105187,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_105182,c_69])).

%------------------------------------------------------------------------------
