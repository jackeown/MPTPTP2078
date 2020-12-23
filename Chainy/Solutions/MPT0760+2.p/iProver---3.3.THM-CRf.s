%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0760+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:52 EST 2020

% Result     : Theorem 34.12s
% Output     : CNFRefutation 34.12s
% Verified   : 
% Statistics : Number of formulae       :   41 (  55 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :  163 ( 207 expanded)
%              Number of equality atoms :   52 (  68 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f833,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1805,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f833])).

fof(f1806,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1805])).

fof(f4257,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1806])).

fof(f1126,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2229,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1126])).

fof(f2968,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2229])).

fof(f2969,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2968])).

fof(f2970,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2969])).

fof(f2971,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK272(X0,X1,X2),X1),X0)
          | sK272(X0,X1,X2) = X1
          | ~ r2_hidden(sK272(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK272(X0,X1,X2),X1),X0)
            & sK272(X0,X1,X2) != X1 )
          | r2_hidden(sK272(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2972,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK272(X0,X1,X2),X1),X0)
                | sK272(X0,X1,X2) = X1
                | ~ r2_hidden(sK272(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK272(X0,X1,X2),X1),X0)
                  & sK272(X0,X1,X2) != X1 )
                | r2_hidden(sK272(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK272])],[f2970,f2971])).

fof(f4859,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2972])).

fof(f5781,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f4859])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1165,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f2309,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK32(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f2310,plain,(
    ! [X0] :
      ( r2_hidden(sK32(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK32])],[f1165,f2309])).

fof(f3040,plain,(
    ! [X0] :
      ( r2_hidden(sK32(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2310])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2982,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f4910,plain,(
    ! [X0] :
      ( r2_hidden(sK32(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f3040,f2982])).

fof(f1129,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k1_wellord1(X1,X0)
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1130,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k1_wellord1(X1,X0)
          | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f1129])).

fof(f2231,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1130])).

fof(f2232,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f2231])).

fof(f2973,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != k1_wellord1(X1,X0)
        & ~ r2_hidden(X0,k3_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_xboole_0 != k1_wellord1(sK274,sK273)
      & ~ r2_hidden(sK273,k3_relat_1(sK274))
      & v1_relat_1(sK274) ) ),
    introduced(choice_axiom,[])).

fof(f2974,plain,
    ( k1_xboole_0 != k1_wellord1(sK274,sK273)
    & ~ r2_hidden(sK273,k3_relat_1(sK274))
    & v1_relat_1(sK274) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK273,sK274])],[f2232,f2973])).

fof(f4867,plain,(
    k1_xboole_0 != k1_wellord1(sK274,sK273) ),
    inference(cnf_transformation,[],[f2974])).

fof(f5539,plain,(
    o_0_0_xboole_0 != k1_wellord1(sK274,sK273) ),
    inference(definition_unfolding,[],[f4867,f2982])).

fof(f4866,plain,(
    ~ r2_hidden(sK273,k3_relat_1(sK274)) ),
    inference(cnf_transformation,[],[f2974])).

fof(f4865,plain,(
    v1_relat_1(sK274) ),
    inference(cnf_transformation,[],[f2974])).

cnf(c_1267,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4257])).

cnf(c_134859,plain,
    ( ~ r2_hidden(k4_tarski(sK32(k1_wellord1(sK274,sK273)),sK273),sK274)
    | r2_hidden(sK273,k3_relat_1(sK274))
    | ~ v1_relat_1(sK274) ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_1872,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f5781])).

cnf(c_109410,plain,
    ( r2_hidden(k4_tarski(sK32(k1_wellord1(sK274,sK273)),sK273),sK274)
    | ~ r2_hidden(sK32(k1_wellord1(sK274,sK273)),k1_wellord1(sK274,sK273))
    | ~ v1_relat_1(sK274) ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_66,plain,
    ( r2_hidden(sK32(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f4910])).

cnf(c_97660,plain,
    ( r2_hidden(sK32(k1_wellord1(sK274,sK273)),k1_wellord1(sK274,sK273))
    | o_0_0_xboole_0 = k1_wellord1(sK274,sK273) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_1875,negated_conjecture,
    ( o_0_0_xboole_0 != k1_wellord1(sK274,sK273) ),
    inference(cnf_transformation,[],[f5539])).

cnf(c_1876,negated_conjecture,
    ( ~ r2_hidden(sK273,k3_relat_1(sK274)) ),
    inference(cnf_transformation,[],[f4866])).

cnf(c_1877,negated_conjecture,
    ( v1_relat_1(sK274) ),
    inference(cnf_transformation,[],[f4865])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_134859,c_109410,c_97660,c_1875,c_1876,c_1877])).

%------------------------------------------------------------------------------
