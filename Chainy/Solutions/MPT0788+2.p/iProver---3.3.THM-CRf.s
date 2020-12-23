%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0788+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:53 EST 2020

% Result     : Theorem 51.75s
% Output     : CNFRefutation 51.75s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 224 expanded)
%              Number of clauses        :   37 (  55 expanded)
%              Number of leaves         :    6 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  349 (1601 expanded)
%              Number of equality atoms :  120 ( 376 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2424,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f2425,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2424])).

fof(f3220,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2425])).

fof(f5855,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f3220])).

fof(f1172,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
            | X0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1173,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
              | X0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1172])).

fof(f2340,plain,(
    ? [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <~> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1173])).

fof(f2341,plain,(
    ? [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <~> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f2340])).

fof(f3146,plain,(
    ? [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
          & X0 != X1 )
        | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & ( r2_hidden(X0,k1_wellord1(X2,X1))
        | X0 = X1
        | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f2341])).

fof(f3147,plain,(
    ? [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
          & X0 != X1 )
        | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & ( r2_hidden(X0,k1_wellord1(X2,X1))
        | X0 = X1
        | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f3146])).

fof(f3148,plain,
    ( ? [X0,X1,X2] :
        ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
            & X0 != X1 )
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1
          | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ( ~ r2_hidden(sK295,k1_wellord1(sK297,sK296))
          & sK295 != sK296 )
        | ~ r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) )
      & ( r2_hidden(sK295,k1_wellord1(sK297,sK296))
        | sK295 = sK296
        | r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) )
      & r2_hidden(sK296,k3_relat_1(sK297))
      & r2_hidden(sK295,k3_relat_1(sK297))
      & v2_wellord1(sK297)
      & v1_relat_1(sK297) ) ),
    introduced(choice_axiom,[])).

fof(f3149,plain,
    ( ( ( ~ r2_hidden(sK295,k1_wellord1(sK297,sK296))
        & sK295 != sK296 )
      | ~ r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) )
    & ( r2_hidden(sK295,k1_wellord1(sK297,sK296))
      | sK295 = sK296
      | r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) )
    & r2_hidden(sK296,k3_relat_1(sK297))
    & r2_hidden(sK295,k3_relat_1(sK297))
    & v2_wellord1(sK297)
    & v1_relat_1(sK297) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK295,sK296,sK297])],[f3147,f3148])).

fof(f5149,plain,
    ( r2_hidden(sK295,k1_wellord1(sK297,sK296))
    | sK295 = sK296
    | r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) ),
    inference(cnf_transformation,[],[f3149])).

fof(f1171,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2338,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1171])).

fof(f2339,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2338])).

fof(f3145,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f2339])).

fof(f5144,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f3145])).

fof(f5145,plain,(
    v1_relat_1(sK297) ),
    inference(cnf_transformation,[],[f3149])).

fof(f5146,plain,(
    v2_wellord1(sK297) ),
    inference(cnf_transformation,[],[f3149])).

fof(f5147,plain,(
    r2_hidden(sK295,k3_relat_1(sK297)) ),
    inference(cnf_transformation,[],[f3149])).

fof(f5148,plain,(
    r2_hidden(sK296,k3_relat_1(sK297)) ),
    inference(cnf_transformation,[],[f3149])).

fof(f5150,plain,
    ( sK295 != sK296
    | ~ r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) ),
    inference(cnf_transformation,[],[f3149])).

fof(f5143,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f3145])).

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

fof(f2281,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1130])).

fof(f3088,plain,(
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
    inference(nnf_transformation,[],[f2281])).

fof(f3089,plain,(
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
    inference(flattening,[],[f3088])).

fof(f3090,plain,(
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
    inference(rectify,[],[f3089])).

fof(f3091,plain,(
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

fof(f3092,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK273])],[f3090,f3091])).

fof(f5048,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3092])).

fof(f6084,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f5048])).

fof(f5151,plain,
    ( ~ r2_hidden(sK295,k1_wellord1(sK297,sK296))
    | ~ r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) ),
    inference(cnf_transformation,[],[f3149])).

fof(f5047,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3092])).

fof(f6085,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f5047])).

cnf(c_69,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5855])).

cnf(c_89782,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_1978,negated_conjecture,
    ( r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296))
    | r2_hidden(sK295,k1_wellord1(sK297,sK296))
    | sK295 = sK296 ),
    inference(cnf_transformation,[],[f5149])).

cnf(c_88409,plain,
    ( sK295 = sK296
    | r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) = iProver_top
    | r2_hidden(sK295,k1_wellord1(sK297,sK296)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1978])).

cnf(c_1974,plain,
    ( ~ r1_tarski(k1_wellord1(X0,X1),k1_wellord1(X0,X2))
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | r2_hidden(k4_tarski(X1,X2),X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5144])).

cnf(c_88413,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k1_wellord1(X0,X2)) != iProver_top
    | r2_hidden(X2,k3_relat_1(X0)) != iProver_top
    | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),X0) = iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_197799,plain,
    ( sK296 = sK295
    | r2_hidden(k4_tarski(sK295,sK296),sK297) = iProver_top
    | r2_hidden(sK296,k3_relat_1(sK297)) != iProver_top
    | r2_hidden(sK295,k1_wellord1(sK297,sK296)) = iProver_top
    | r2_hidden(sK295,k3_relat_1(sK297)) != iProver_top
    | v2_wellord1(sK297) != iProver_top
    | v1_relat_1(sK297) != iProver_top ),
    inference(superposition,[status(thm)],[c_88409,c_88413])).

cnf(c_1982,negated_conjecture,
    ( v1_relat_1(sK297) ),
    inference(cnf_transformation,[],[f5145])).

cnf(c_1989,plain,
    ( v1_relat_1(sK297) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1982])).

cnf(c_1981,negated_conjecture,
    ( v2_wellord1(sK297) ),
    inference(cnf_transformation,[],[f5146])).

cnf(c_1990,plain,
    ( v2_wellord1(sK297) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1981])).

cnf(c_1980,negated_conjecture,
    ( r2_hidden(sK295,k3_relat_1(sK297)) ),
    inference(cnf_transformation,[],[f5147])).

cnf(c_1991,plain,
    ( r2_hidden(sK295,k3_relat_1(sK297)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_1979,negated_conjecture,
    ( r2_hidden(sK296,k3_relat_1(sK297)) ),
    inference(cnf_transformation,[],[f5148])).

cnf(c_1992,plain,
    ( r2_hidden(sK296,k3_relat_1(sK297)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1979])).

cnf(c_1977,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296))
    | sK295 != sK296 ),
    inference(cnf_transformation,[],[f5150])).

cnf(c_1994,plain,
    ( sK295 != sK296
    | r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1977])).

cnf(c_1975,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k1_wellord1(X0,X2))
    | ~ r2_hidden(X2,k3_relat_1(X0))
    | ~ r2_hidden(X1,k3_relat_1(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),X0)
    | ~ v2_wellord1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f5143])).

cnf(c_93210,plain,
    ( r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296))
    | ~ r2_hidden(k4_tarski(sK295,sK296),sK297)
    | ~ r2_hidden(sK296,k3_relat_1(sK297))
    | ~ r2_hidden(sK295,k3_relat_1(sK297))
    | ~ v2_wellord1(sK297)
    | ~ v1_relat_1(sK297) ),
    inference(instantiation,[status(thm)],[c_1975])).

cnf(c_93211,plain,
    ( r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) = iProver_top
    | r2_hidden(k4_tarski(sK295,sK296),sK297) != iProver_top
    | r2_hidden(sK296,k3_relat_1(sK297)) != iProver_top
    | r2_hidden(sK295,k3_relat_1(sK297)) != iProver_top
    | v2_wellord1(sK297) != iProver_top
    | v1_relat_1(sK297) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_93210])).

cnf(c_1880,plain,
    ( r2_hidden(X0,k1_wellord1(X1,X2))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f6084])).

cnf(c_92787,plain,
    ( ~ r2_hidden(k4_tarski(sK295,sK296),X0)
    | r2_hidden(sK295,k1_wellord1(X0,sK296))
    | ~ v1_relat_1(X0)
    | sK295 = sK296 ),
    inference(instantiation,[status(thm)],[c_1880])).

cnf(c_165433,plain,
    ( ~ r2_hidden(k4_tarski(sK295,sK296),sK297)
    | r2_hidden(sK295,k1_wellord1(sK297,sK296))
    | ~ v1_relat_1(sK297)
    | sK295 = sK296 ),
    inference(instantiation,[status(thm)],[c_92787])).

cnf(c_165434,plain,
    ( sK295 = sK296
    | r2_hidden(k4_tarski(sK295,sK296),sK297) != iProver_top
    | r2_hidden(sK295,k1_wellord1(sK297,sK296)) = iProver_top
    | v1_relat_1(sK297) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165433])).

cnf(c_88412,plain,
    ( r1_tarski(k1_wellord1(X0,X1),k1_wellord1(X0,X2)) = iProver_top
    | r2_hidden(X2,k3_relat_1(X0)) != iProver_top
    | r2_hidden(X1,k3_relat_1(X0)) != iProver_top
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v2_wellord1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1975])).

cnf(c_1976,negated_conjecture,
    ( ~ r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296))
    | ~ r2_hidden(sK295,k1_wellord1(sK297,sK296)) ),
    inference(cnf_transformation,[],[f5151])).

cnf(c_88411,plain,
    ( r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) != iProver_top
    | r2_hidden(sK295,k1_wellord1(sK297,sK296)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1976])).

cnf(c_189034,plain,
    ( r2_hidden(k4_tarski(sK295,sK296),sK297) != iProver_top
    | r2_hidden(sK296,k3_relat_1(sK297)) != iProver_top
    | r2_hidden(sK295,k1_wellord1(sK297,sK296)) != iProver_top
    | r2_hidden(sK295,k3_relat_1(sK297)) != iProver_top
    | v2_wellord1(sK297) != iProver_top
    | v1_relat_1(sK297) != iProver_top ),
    inference(superposition,[status(thm)],[c_88412,c_88411])).

cnf(c_1881,plain,
    ( ~ r2_hidden(X0,k1_wellord1(X1,X2))
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f6085])).

cnf(c_96444,plain,
    ( r2_hidden(k4_tarski(sK295,sK296),sK297)
    | ~ r2_hidden(sK295,k1_wellord1(sK297,sK296))
    | ~ v1_relat_1(sK297) ),
    inference(instantiation,[status(thm)],[c_1881])).

cnf(c_96445,plain,
    ( r2_hidden(k4_tarski(sK295,sK296),sK297) = iProver_top
    | r2_hidden(sK295,k1_wellord1(sK297,sK296)) != iProver_top
    | v1_relat_1(sK297) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_96444])).

cnf(c_192576,plain,
    ( r2_hidden(sK295,k1_wellord1(sK297,sK296)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_189034,c_1989,c_1990,c_1991,c_1992,c_96445])).

cnf(c_199598,plain,
    ( sK296 = sK295 ),
    inference(global_propositional_subsumption,[status(thm)],[c_197799,c_1989,c_1990,c_1991,c_1992,c_1994,c_93211,c_96445,c_165434,c_189034])).

cnf(c_88410,plain,
    ( sK295 != sK296
    | r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK296)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1977])).

cnf(c_199602,plain,
    ( sK295 != sK295
    | r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK295)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_199598,c_88410])).

cnf(c_199604,plain,
    ( r1_tarski(k1_wellord1(sK297,sK295),k1_wellord1(sK297,sK295)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_199602])).

cnf(c_200461,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_89782,c_199604])).

%------------------------------------------------------------------------------
