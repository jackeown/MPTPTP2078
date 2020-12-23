%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0767+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:52 EST 2020

% Result     : Theorem 47.76s
% Output     : CNFRefutation 47.76s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 ( 213 expanded)
%              Number of equality atoms :   33 (  33 expanded)
%              Maximal formula depth    :   12 (   6 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1827,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f833])).

fof(f1828,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1827])).

fof(f4356,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1828])).

fof(f1130,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2255,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1130])).

fof(f3023,plain,(
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
    inference(nnf_transformation,[],[f2255])).

fof(f3024,plain,(
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
    inference(flattening,[],[f3023])).

fof(f3025,plain,(
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
    inference(rectify,[],[f3024])).

fof(f3026,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK273(X0,X1,X2),X1),X0)
          | sK273(X0,X1,X2) = X1
          | ~ r2_hidden(sK273(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK273(X0,X1,X2),X1),X0)
            & sK273(X0,X1,X2) != X1 )
          | r2_hidden(sK273(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f3027,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK273(X0,X1,X2),X1),X0)
                | sK273(X0,X1,X2) = X1
                | ~ r2_hidden(sK273(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK273(X0,X1,X2),X1),X0)
                  & sK273(X0,X1,X2) != X1 )
                | r2_hidden(sK273(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK273])],[f3025,f3026])).

fof(f4968,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3027])).

fof(f5961,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f4968])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1177,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f2318,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1177])).

fof(f2319,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f2318])).

fof(f2320,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK21(X0,X1),X1)
        & r2_hidden(sK21(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2321,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK21(X0,X1),X1)
          & r2_hidden(sK21(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f2319,f2320])).

fof(f3084,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK21(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f2321])).

fof(f3085,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK21(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2321])).

fof(f1146,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1147,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f1146])).

fof(f2274,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1147])).

fof(f3069,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_wellord1(sK290,sK289),k3_relat_1(sK290))
      & v1_relat_1(sK290) ) ),
    introduced(choice_axiom,[])).

fof(f3070,plain,
    ( ~ r1_tarski(k1_wellord1(sK290,sK289),k3_relat_1(sK290))
    & v1_relat_1(sK290) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK289,sK290])],[f2274,f3069])).

fof(f5028,plain,(
    ~ r1_tarski(k1_wellord1(sK290,sK289),k3_relat_1(sK290)) ),
    inference(cnf_transformation,[],[f3070])).

fof(f5027,plain,(
    v1_relat_1(sK290) ),
    inference(cnf_transformation,[],[f3070])).

cnf(c_1268,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4356])).

cnf(c_144754,plain,
    ( ~ r2_hidden(k4_tarski(sK21(k1_wellord1(sK290,sK289),k3_relat_1(sK290)),sK289),sK290)
    | r2_hidden(sK21(k1_wellord1(sK290,sK289),k3_relat_1(sK290)),k3_relat_1(sK290))
    | ~ v1_relat_1(sK290) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_1881,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f5961])).

cnf(c_117168,plain,
    ( r2_hidden(k4_tarski(sK21(k1_wellord1(sK290,sK289),k3_relat_1(sK290)),sK289),sK290)
    | ~ r2_hidden(sK21(k1_wellord1(sK290,sK289),k3_relat_1(sK290)),k1_wellord1(sK290,sK289))
    | ~ v1_relat_1(sK290) ),
    inference(instantiation,[status(thm)],[c_1881])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK21(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3084])).

cnf(c_102668,plain,
    ( r1_tarski(k1_wellord1(sK290,sK289),k3_relat_1(sK290))
    | r2_hidden(sK21(k1_wellord1(sK290,sK289),k3_relat_1(sK290)),k1_wellord1(sK290,sK289)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK21(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3085])).

cnf(c_102660,plain,
    ( r1_tarski(k1_wellord1(sK290,sK289),k3_relat_1(sK290))
    | ~ r2_hidden(sK21(k1_wellord1(sK290,sK289),k3_relat_1(sK290)),k3_relat_1(sK290)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1937,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(sK290,sK289),k3_relat_1(sK290)) ),
    inference(cnf_transformation,[],[f5028])).

cnf(c_1938,negated_conjecture,
    ( v1_relat_1(sK290) ),
    inference(cnf_transformation,[],[f5027])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_144754,c_117168,c_102668,c_102660,c_1937,c_1938])).

%------------------------------------------------------------------------------
