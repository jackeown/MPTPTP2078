%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0766+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:52 EST 2020

% Result     : Theorem 27.42s
% Output     : CNFRefutation 27.42s
% Verified   : 
% Statistics : Number of formulae       :   46 (  99 expanded)
%              Number of clauses        :   19 (  21 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  249 ( 842 expanded)
%              Number of equality atoms :   33 (  94 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1139,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2262,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1139])).

fof(f3045,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2262])).

fof(f3046,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f3045])).

fof(f3047,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK280(X0),sK280(X0)),X0)
        & r2_hidden(sK280(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3048,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK280(X0),sK280(X0)),X0)
            & r2_hidden(sK280(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK280])],[f3046,f3047])).

fof(f5003,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,X2),X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3048])).

fof(f1145,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                          & X1 != X3
                          & r2_hidden(k4_tarski(X1,X3),X0)
                          & r2_hidden(X3,k3_relat_1(X0)) )
                    & r2_hidden(k4_tarski(X1,X2),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
              & ? [X2] :
                  ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                  & r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1146,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X2] :
                    ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1145])).

fof(f1170,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                    & r2_hidden(X4,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(rectify,[],[f1146])).

fof(f2271,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1170])).

fof(f2272,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f2271])).

fof(f3068,plain,(
    ! [X0,X1] :
      ( ? [X4] :
          ( ~ r2_hidden(k4_tarski(X4,X1),X0)
          & r2_hidden(X4,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK291,X1),X0)
        & r2_hidden(sK291,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3067,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X0)
          & X1 != X3
          & r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(X3,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(X2,sK290(X2)),X0)
        & sK290(X2) != X1
        & r2_hidden(k4_tarski(X1,sK290(X2)),X0)
        & r2_hidden(sK290(X2),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3066,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                & sK289 != X3
                & r2_hidden(k4_tarski(sK289,X3),X0)
                & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(k4_tarski(sK289,X2),X0)
            | ~ r2_hidden(X2,k3_relat_1(X0)) )
        & ? [X4] :
            ( ~ r2_hidden(k4_tarski(X4,sK289),X0)
            & r2_hidden(X4,k3_relat_1(X0)) )
        & r2_hidden(sK289,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3065,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                    & X1 != X3
                    & r2_hidden(k4_tarski(X1,X3),X0)
                    & r2_hidden(X3,k3_relat_1(X0)) )
                | ~ r2_hidden(k4_tarski(X1,X2),X0)
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & ? [X4] :
                ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                & r2_hidden(X4,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) )
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK288)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),sK288)
                  & r2_hidden(X3,k3_relat_1(sK288)) )
              | ~ r2_hidden(k4_tarski(X1,X2),sK288)
              | ~ r2_hidden(X2,k3_relat_1(sK288)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),sK288)
              & r2_hidden(X4,k3_relat_1(sK288)) )
          & r2_hidden(X1,k3_relat_1(sK288)) )
      & v2_wellord1(sK288)
      & v1_relat_1(sK288) ) ),
    introduced(choice_axiom,[])).

fof(f3069,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK290(X2)),sK288)
          & sK289 != sK290(X2)
          & r2_hidden(k4_tarski(sK289,sK290(X2)),sK288)
          & r2_hidden(sK290(X2),k3_relat_1(sK288)) )
        | ~ r2_hidden(k4_tarski(sK289,X2),sK288)
        | ~ r2_hidden(X2,k3_relat_1(sK288)) )
    & ~ r2_hidden(k4_tarski(sK291,sK289),sK288)
    & r2_hidden(sK291,k3_relat_1(sK288))
    & r2_hidden(sK289,k3_relat_1(sK288))
    & v2_wellord1(sK288)
    & v1_relat_1(sK288) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK288,sK289,sK290,sK291])],[f2272,f3068,f3067,f3066,f3065])).

fof(f5029,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(sK289,sK290(X2)),sK288)
      | ~ r2_hidden(k4_tarski(sK289,X2),sK288)
      | ~ r2_hidden(X2,k3_relat_1(sK288)) ) ),
    inference(cnf_transformation,[],[f3069])).

fof(f5031,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK290(X2)),sK288)
      | ~ r2_hidden(k4_tarski(sK289,X2),sK288)
      | ~ r2_hidden(X2,k3_relat_1(sK288)) ) ),
    inference(cnf_transformation,[],[f3069])).

fof(f5025,plain,(
    r2_hidden(sK289,k3_relat_1(sK288)) ),
    inference(cnf_transformation,[],[f3069])).

fof(f1133,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2257,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1133])).

fof(f3036,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2257])).

fof(f3037,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3036])).

fof(f4982,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3037])).

fof(f5024,plain,(
    v2_wellord1(sK288) ),
    inference(cnf_transformation,[],[f3069])).

fof(f5023,plain,(
    v1_relat_1(sK288) ),
    inference(cnf_transformation,[],[f3069])).

cnf(c_1916,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,X0),X1)
    | ~ v1_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f5003])).

cnf(c_89289,plain,
    ( r2_hidden(X0,k3_relat_1(X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,X0),X1) = iProver_top
    | v1_relat_2(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1916])).

cnf(c_1936,negated_conjecture,
    ( ~ r2_hidden(X0,k3_relat_1(sK288))
    | ~ r2_hidden(k4_tarski(sK289,X0),sK288)
    | r2_hidden(k4_tarski(sK289,sK290(X0)),sK288) ),
    inference(cnf_transformation,[],[f5029])).

cnf(c_89273,plain,
    ( r2_hidden(X0,k3_relat_1(sK288)) != iProver_top
    | r2_hidden(k4_tarski(sK289,X0),sK288) != iProver_top
    | r2_hidden(k4_tarski(sK289,sK290(X0)),sK288) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_1934,negated_conjecture,
    ( ~ r2_hidden(X0,k3_relat_1(sK288))
    | ~ r2_hidden(k4_tarski(X0,sK290(X0)),sK288)
    | ~ r2_hidden(k4_tarski(sK289,X0),sK288) ),
    inference(cnf_transformation,[],[f5031])).

cnf(c_89275,plain,
    ( r2_hidden(X0,k3_relat_1(sK288)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK290(X0)),sK288) != iProver_top
    | r2_hidden(k4_tarski(sK289,X0),sK288) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_104509,plain,
    ( r2_hidden(k4_tarski(sK289,sK289),sK288) != iProver_top
    | r2_hidden(sK289,k3_relat_1(sK288)) != iProver_top ),
    inference(superposition,[status(thm)],[c_89273,c_89275])).

cnf(c_1940,negated_conjecture,
    ( r2_hidden(sK289,k3_relat_1(sK288)) ),
    inference(cnf_transformation,[],[f5025])).

cnf(c_1952,plain,
    ( r2_hidden(sK289,k3_relat_1(sK288)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1940])).

cnf(c_104537,plain,
    ( r2_hidden(k4_tarski(sK289,sK289),sK288) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_104509,c_1952])).

cnf(c_112084,plain,
    ( r2_hidden(sK289,k3_relat_1(sK288)) != iProver_top
    | v1_relat_2(sK288) != iProver_top
    | v1_relat_1(sK288) != iProver_top ),
    inference(superposition,[status(thm)],[c_89289,c_104537])).

cnf(c_1898,plain,
    ( v1_relat_2(X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4982])).

cnf(c_1941,negated_conjecture,
    ( v2_wellord1(sK288) ),
    inference(cnf_transformation,[],[f5024])).

cnf(c_22515,plain,
    ( v1_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK288 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1898,c_1941])).

cnf(c_22516,plain,
    ( v1_relat_2(sK288)
    | ~ v1_relat_1(sK288) ),
    inference(unflattening,[status(thm)],[c_22515])).

cnf(c_22517,plain,
    ( v1_relat_2(sK288) = iProver_top
    | v1_relat_1(sK288) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22516])).

cnf(c_1942,negated_conjecture,
    ( v1_relat_1(sK288) ),
    inference(cnf_transformation,[],[f5023])).

cnf(c_1950,plain,
    ( v1_relat_1(sK288) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1942])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_112084,c_22517,c_1952,c_1950])).

%------------------------------------------------------------------------------
