%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:37 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 145 expanded)
%              Number of clauses        :   37 (  40 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :  354 ( 804 expanded)
%              Number of equality atoms :  185 ( 437 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f19,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4) != X0
            & sK1(X0,X1,X2,X3,X4) != X1
            & sK1(X0,X1,X2,X3,X4) != X2
            & sK1(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4),X4) )
        & ( sK1(X0,X1,X2,X3,X4) = X0
          | sK1(X0,X1,X2,X3,X4) = X1
          | sK1(X0,X1,X2,X3,X4) = X2
          | sK1(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK1(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK1(X0,X1,X2,X3,X4) != X0
              & sK1(X0,X1,X2,X3,X4) != X1
              & sK1(X0,X1,X2,X3,X4) != X2
              & sK1(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4),X4) )
          & ( sK1(X0,X1,X2,X3,X4) = X0
            | sK1(X0,X1,X2,X3,X4) = X1
            | sK1(X0,X1,X2,X3,X4) = X2
            | sK1(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK1(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X0 = X6
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | ~ r2_hidden(X6,X4)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK5,sK4) != sK3
      & r2_hidden(sK4,sK2)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
      & v1_funct_2(sK5,sK2,k1_tarski(sK3))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k1_funct_1(sK5,sK4) != sK3
    & r2_hidden(sK4,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))
    & v1_funct_2(sK5,sK2,k1_tarski(sK3))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f15,f24])).

fof(f45,plain,(
    v1_funct_2(sK5,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f49])).

fof(f52,plain,(
    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f44,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( r2_hidden(X6,X4)
      | ~ sP0(X0,X1,X2,X6,X4) ) ),
    inference(equality_resolution,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f10,f16])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f40])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1721,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2140,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1721])).

cnf(c_3079,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_3081,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3079])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ r2_hidden(X5,X4)
    | X5 = X3
    | X5 = X2
    | X5 = X1
    | X5 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2150,plain,
    ( ~ sP0(X0,X1,X2,sK3,X3)
    | ~ r2_hidden(k1_funct_1(sK5,sK4),X3)
    | k1_funct_1(sK5,sK4) = X0
    | k1_funct_1(sK5,sK4) = X2
    | k1_funct_1(sK5,sK4) = X1
    | k1_funct_1(sK5,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2501,plain,
    ( ~ sP0(X0,X1,X2,sK3,k2_enumset1(sK3,X2,X1,X0))
    | ~ r2_hidden(k1_funct_1(sK5,sK4),k2_enumset1(sK3,X2,X1,X0))
    | k1_funct_1(sK5,sK4) = X0
    | k1_funct_1(sK5,sK4) = X2
    | k1_funct_1(sK5,sK4) = X1
    | k1_funct_1(sK5,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_2150])).

cnf(c_2504,plain,
    ( ~ sP0(sK3,sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ r2_hidden(k1_funct_1(sK5,sK4),k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_funct_1(sK5,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_2501])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_220,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_221,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK5,X2),X1)
    | ~ v1_funct_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_225,plain,
    ( r2_hidden(k1_funct_1(sK5,X2),X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK5,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_221,c_19])).

cnf(c_226,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK5,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_225])).

cnf(c_253,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK5,X0),X2)
    | k2_enumset1(sK3,sK3,sK3,sK3) != X2
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X1
    | sK5 != sK5
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_226])).

cnf(c_254,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK5,X0),k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_967,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK5,X0),k2_enumset1(sK3,sK3,sK3,sK3))
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_254])).

cnf(c_2105,plain,
    ( r2_hidden(k1_funct_1(sK5,sK4),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK4,sK2)
    | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | r2_hidden(X3,X4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_12,plain,
    ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_785,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | k2_enumset1(X4,X5,X7,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_786,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_788,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_764,plain,
    ( ~ r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X0 = X3
    | X0 = X5
    | X0 = X7
    | X0 = X9
    | k2_enumset1(X2,X4,X6,X8) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_765,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
    | X0 = X2
    | X0 = X1
    | X0 = X3
    | X0 = X4 ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_767,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_209,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_210,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_212,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_31,plain,
    ( sP0(sK3,sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_15,negated_conjecture,
    ( k1_funct_1(sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK4,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3081,c_2504,c_2105,c_788,c_767,c_212,c_31,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.45/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.45/1.00  
% 1.45/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.45/1.00  
% 1.45/1.00  ------  iProver source info
% 1.45/1.00  
% 1.45/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.45/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.45/1.00  git: non_committed_changes: false
% 1.45/1.00  git: last_make_outside_of_git: false
% 1.45/1.00  
% 1.45/1.00  ------ 
% 1.45/1.00  
% 1.45/1.00  ------ Input Options
% 1.45/1.00  
% 1.45/1.00  --out_options                           all
% 1.45/1.00  --tptp_safe_out                         true
% 1.45/1.00  --problem_path                          ""
% 1.45/1.00  --include_path                          ""
% 1.45/1.00  --clausifier                            res/vclausify_rel
% 1.45/1.00  --clausifier_options                    --mode clausify
% 1.45/1.00  --stdin                                 false
% 1.45/1.00  --stats_out                             all
% 1.45/1.00  
% 1.45/1.00  ------ General Options
% 1.45/1.00  
% 1.45/1.00  --fof                                   false
% 1.45/1.00  --time_out_real                         305.
% 1.45/1.00  --time_out_virtual                      -1.
% 1.45/1.00  --symbol_type_check                     false
% 1.45/1.00  --clausify_out                          false
% 1.45/1.00  --sig_cnt_out                           false
% 1.45/1.00  --trig_cnt_out                          false
% 1.45/1.00  --trig_cnt_out_tolerance                1.
% 1.45/1.00  --trig_cnt_out_sk_spl                   false
% 1.45/1.00  --abstr_cl_out                          false
% 1.45/1.00  
% 1.45/1.00  ------ Global Options
% 1.45/1.00  
% 1.45/1.00  --schedule                              default
% 1.45/1.00  --add_important_lit                     false
% 1.45/1.00  --prop_solver_per_cl                    1000
% 1.45/1.00  --min_unsat_core                        false
% 1.45/1.00  --soft_assumptions                      false
% 1.45/1.00  --soft_lemma_size                       3
% 1.45/1.00  --prop_impl_unit_size                   0
% 1.45/1.00  --prop_impl_unit                        []
% 1.45/1.00  --share_sel_clauses                     true
% 1.45/1.00  --reset_solvers                         false
% 1.45/1.00  --bc_imp_inh                            [conj_cone]
% 1.45/1.00  --conj_cone_tolerance                   3.
% 1.45/1.00  --extra_neg_conj                        none
% 1.45/1.00  --large_theory_mode                     true
% 1.45/1.00  --prolific_symb_bound                   200
% 1.45/1.00  --lt_threshold                          2000
% 1.45/1.00  --clause_weak_htbl                      true
% 1.45/1.00  --gc_record_bc_elim                     false
% 1.45/1.00  
% 1.45/1.00  ------ Preprocessing Options
% 1.45/1.00  
% 1.45/1.00  --preprocessing_flag                    true
% 1.45/1.00  --time_out_prep_mult                    0.1
% 1.45/1.00  --splitting_mode                        input
% 1.45/1.00  --splitting_grd                         true
% 1.45/1.00  --splitting_cvd                         false
% 1.45/1.00  --splitting_cvd_svl                     false
% 1.45/1.00  --splitting_nvd                         32
% 1.45/1.00  --sub_typing                            true
% 1.45/1.00  --prep_gs_sim                           true
% 1.45/1.00  --prep_unflatten                        true
% 1.45/1.00  --prep_res_sim                          true
% 1.45/1.00  --prep_upred                            true
% 1.45/1.00  --prep_sem_filter                       exhaustive
% 1.45/1.00  --prep_sem_filter_out                   false
% 1.45/1.00  --pred_elim                             true
% 1.45/1.00  --res_sim_input                         true
% 1.45/1.00  --eq_ax_congr_red                       true
% 1.45/1.00  --pure_diseq_elim                       true
% 1.45/1.00  --brand_transform                       false
% 1.45/1.00  --non_eq_to_eq                          false
% 1.45/1.00  --prep_def_merge                        true
% 1.45/1.00  --prep_def_merge_prop_impl              false
% 1.45/1.00  --prep_def_merge_mbd                    true
% 1.45/1.00  --prep_def_merge_tr_red                 false
% 1.45/1.00  --prep_def_merge_tr_cl                  false
% 1.45/1.00  --smt_preprocessing                     true
% 1.45/1.00  --smt_ac_axioms                         fast
% 1.45/1.00  --preprocessed_out                      false
% 1.45/1.00  --preprocessed_stats                    false
% 1.45/1.00  
% 1.45/1.00  ------ Abstraction refinement Options
% 1.45/1.00  
% 1.45/1.00  --abstr_ref                             []
% 1.45/1.00  --abstr_ref_prep                        false
% 1.45/1.00  --abstr_ref_until_sat                   false
% 1.45/1.00  --abstr_ref_sig_restrict                funpre
% 1.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.45/1.00  --abstr_ref_under                       []
% 1.45/1.00  
% 1.45/1.00  ------ SAT Options
% 1.45/1.00  
% 1.45/1.00  --sat_mode                              false
% 1.45/1.00  --sat_fm_restart_options                ""
% 1.45/1.00  --sat_gr_def                            false
% 1.45/1.00  --sat_epr_types                         true
% 1.45/1.00  --sat_non_cyclic_types                  false
% 1.45/1.00  --sat_finite_models                     false
% 1.45/1.00  --sat_fm_lemmas                         false
% 1.45/1.00  --sat_fm_prep                           false
% 1.45/1.00  --sat_fm_uc_incr                        true
% 1.45/1.00  --sat_out_model                         small
% 1.45/1.00  --sat_out_clauses                       false
% 1.45/1.00  
% 1.45/1.00  ------ QBF Options
% 1.45/1.00  
% 1.45/1.00  --qbf_mode                              false
% 1.45/1.00  --qbf_elim_univ                         false
% 1.45/1.00  --qbf_dom_inst                          none
% 1.45/1.00  --qbf_dom_pre_inst                      false
% 1.45/1.00  --qbf_sk_in                             false
% 1.45/1.00  --qbf_pred_elim                         true
% 1.45/1.00  --qbf_split                             512
% 1.45/1.00  
% 1.45/1.00  ------ BMC1 Options
% 1.45/1.00  
% 1.45/1.00  --bmc1_incremental                      false
% 1.45/1.00  --bmc1_axioms                           reachable_all
% 1.45/1.00  --bmc1_min_bound                        0
% 1.45/1.00  --bmc1_max_bound                        -1
% 1.45/1.00  --bmc1_max_bound_default                -1
% 1.45/1.00  --bmc1_symbol_reachability              true
% 1.45/1.00  --bmc1_property_lemmas                  false
% 1.45/1.00  --bmc1_k_induction                      false
% 1.45/1.00  --bmc1_non_equiv_states                 false
% 1.45/1.00  --bmc1_deadlock                         false
% 1.45/1.00  --bmc1_ucm                              false
% 1.45/1.00  --bmc1_add_unsat_core                   none
% 1.45/1.00  --bmc1_unsat_core_children              false
% 1.45/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.45/1.00  --bmc1_out_stat                         full
% 1.45/1.00  --bmc1_ground_init                      false
% 1.45/1.00  --bmc1_pre_inst_next_state              false
% 1.45/1.00  --bmc1_pre_inst_state                   false
% 1.45/1.00  --bmc1_pre_inst_reach_state             false
% 1.45/1.00  --bmc1_out_unsat_core                   false
% 1.45/1.00  --bmc1_aig_witness_out                  false
% 1.45/1.00  --bmc1_verbose                          false
% 1.45/1.00  --bmc1_dump_clauses_tptp                false
% 1.45/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.45/1.00  --bmc1_dump_file                        -
% 1.45/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.45/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.45/1.00  --bmc1_ucm_extend_mode                  1
% 1.45/1.00  --bmc1_ucm_init_mode                    2
% 1.45/1.00  --bmc1_ucm_cone_mode                    none
% 1.45/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.45/1.00  --bmc1_ucm_relax_model                  4
% 1.45/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.45/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.45/1.00  --bmc1_ucm_layered_model                none
% 1.45/1.00  --bmc1_ucm_max_lemma_size               10
% 1.45/1.00  
% 1.45/1.00  ------ AIG Options
% 1.45/1.00  
% 1.45/1.00  --aig_mode                              false
% 1.45/1.00  
% 1.45/1.00  ------ Instantiation Options
% 1.45/1.00  
% 1.45/1.00  --instantiation_flag                    true
% 1.45/1.00  --inst_sos_flag                         false
% 1.45/1.00  --inst_sos_phase                        true
% 1.45/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.45/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.45/1.00  --inst_lit_sel_side                     num_symb
% 1.45/1.00  --inst_solver_per_active                1400
% 1.45/1.00  --inst_solver_calls_frac                1.
% 1.45/1.00  --inst_passive_queue_type               priority_queues
% 1.45/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.45/1.00  --inst_passive_queues_freq              [25;2]
% 1.45/1.00  --inst_dismatching                      true
% 1.45/1.00  --inst_eager_unprocessed_to_passive     true
% 1.45/1.00  --inst_prop_sim_given                   true
% 1.45/1.00  --inst_prop_sim_new                     false
% 1.45/1.00  --inst_subs_new                         false
% 1.45/1.00  --inst_eq_res_simp                      false
% 1.45/1.00  --inst_subs_given                       false
% 1.45/1.00  --inst_orphan_elimination               true
% 1.45/1.00  --inst_learning_loop_flag               true
% 1.45/1.00  --inst_learning_start                   3000
% 1.45/1.00  --inst_learning_factor                  2
% 1.45/1.00  --inst_start_prop_sim_after_learn       3
% 1.45/1.00  --inst_sel_renew                        solver
% 1.45/1.00  --inst_lit_activity_flag                true
% 1.45/1.00  --inst_restr_to_given                   false
% 1.45/1.00  --inst_activity_threshold               500
% 1.45/1.00  --inst_out_proof                        true
% 1.45/1.00  
% 1.45/1.00  ------ Resolution Options
% 1.45/1.00  
% 1.45/1.00  --resolution_flag                       true
% 1.45/1.00  --res_lit_sel                           adaptive
% 1.45/1.00  --res_lit_sel_side                      none
% 1.45/1.00  --res_ordering                          kbo
% 1.45/1.00  --res_to_prop_solver                    active
% 1.45/1.00  --res_prop_simpl_new                    false
% 1.45/1.00  --res_prop_simpl_given                  true
% 1.45/1.00  --res_passive_queue_type                priority_queues
% 1.45/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.45/1.00  --res_passive_queues_freq               [15;5]
% 1.45/1.00  --res_forward_subs                      full
% 1.45/1.00  --res_backward_subs                     full
% 1.45/1.00  --res_forward_subs_resolution           true
% 1.45/1.00  --res_backward_subs_resolution          true
% 1.45/1.00  --res_orphan_elimination                true
% 1.45/1.00  --res_time_limit                        2.
% 1.45/1.00  --res_out_proof                         true
% 1.45/1.00  
% 1.45/1.00  ------ Superposition Options
% 1.45/1.00  
% 1.45/1.00  --superposition_flag                    true
% 1.45/1.00  --sup_passive_queue_type                priority_queues
% 1.45/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.45/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.45/1.00  --demod_completeness_check              fast
% 1.45/1.00  --demod_use_ground                      true
% 1.45/1.00  --sup_to_prop_solver                    passive
% 1.45/1.00  --sup_prop_simpl_new                    true
% 1.45/1.00  --sup_prop_simpl_given                  true
% 1.45/1.00  --sup_fun_splitting                     false
% 1.45/1.00  --sup_smt_interval                      50000
% 1.45/1.00  
% 1.45/1.00  ------ Superposition Simplification Setup
% 1.45/1.00  
% 1.45/1.00  --sup_indices_passive                   []
% 1.45/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.45/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.00  --sup_full_bw                           [BwDemod]
% 1.45/1.00  --sup_immed_triv                        [TrivRules]
% 1.45/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.45/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.00  --sup_immed_bw_main                     []
% 1.45/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.45/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/1.00  
% 1.45/1.00  ------ Combination Options
% 1.45/1.00  
% 1.45/1.00  --comb_res_mult                         3
% 1.45/1.00  --comb_sup_mult                         2
% 1.45/1.00  --comb_inst_mult                        10
% 1.45/1.00  
% 1.45/1.00  ------ Debug Options
% 1.45/1.00  
% 1.45/1.00  --dbg_backtrace                         false
% 1.45/1.00  --dbg_dump_prop_clauses                 false
% 1.45/1.00  --dbg_dump_prop_clauses_file            -
% 1.45/1.00  --dbg_out_stat                          false
% 1.45/1.00  ------ Parsing...
% 1.45/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.45/1.00  
% 1.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.45/1.00  
% 1.45/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.45/1.00  
% 1.45/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.45/1.00  ------ Proving...
% 1.45/1.00  ------ Problem Properties 
% 1.45/1.00  
% 1.45/1.00  
% 1.45/1.00  clauses                                 16
% 1.45/1.00  conjectures                             2
% 1.45/1.00  EPR                                     7
% 1.45/1.00  Horn                                    13
% 1.45/1.00  unary                                   4
% 1.45/1.00  binary                                  5
% 1.45/1.00  lits                                    41
% 1.45/1.00  lits eq                                 15
% 1.45/1.00  fd_pure                                 0
% 1.45/1.00  fd_pseudo                               0
% 1.45/1.00  fd_cond                                 0
% 1.45/1.00  fd_pseudo_cond                          2
% 1.45/1.00  AC symbols                              0
% 1.45/1.00  
% 1.45/1.00  ------ Schedule dynamic 5 is on 
% 1.45/1.00  
% 1.45/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.45/1.00  
% 1.45/1.00  
% 1.45/1.00  ------ 
% 1.45/1.00  Current options:
% 1.45/1.00  ------ 
% 1.45/1.00  
% 1.45/1.00  ------ Input Options
% 1.45/1.00  
% 1.45/1.00  --out_options                           all
% 1.45/1.00  --tptp_safe_out                         true
% 1.45/1.00  --problem_path                          ""
% 1.45/1.00  --include_path                          ""
% 1.45/1.00  --clausifier                            res/vclausify_rel
% 1.45/1.00  --clausifier_options                    --mode clausify
% 1.45/1.00  --stdin                                 false
% 1.45/1.00  --stats_out                             all
% 1.45/1.00  
% 1.45/1.00  ------ General Options
% 1.45/1.00  
% 1.45/1.00  --fof                                   false
% 1.45/1.00  --time_out_real                         305.
% 1.45/1.00  --time_out_virtual                      -1.
% 1.45/1.00  --symbol_type_check                     false
% 1.45/1.00  --clausify_out                          false
% 1.45/1.00  --sig_cnt_out                           false
% 1.45/1.00  --trig_cnt_out                          false
% 1.45/1.00  --trig_cnt_out_tolerance                1.
% 1.45/1.00  --trig_cnt_out_sk_spl                   false
% 1.45/1.00  --abstr_cl_out                          false
% 1.45/1.00  
% 1.45/1.00  ------ Global Options
% 1.45/1.00  
% 1.45/1.00  --schedule                              default
% 1.45/1.00  --add_important_lit                     false
% 1.45/1.00  --prop_solver_per_cl                    1000
% 1.45/1.00  --min_unsat_core                        false
% 1.45/1.00  --soft_assumptions                      false
% 1.45/1.00  --soft_lemma_size                       3
% 1.45/1.00  --prop_impl_unit_size                   0
% 1.45/1.00  --prop_impl_unit                        []
% 1.45/1.00  --share_sel_clauses                     true
% 1.45/1.00  --reset_solvers                         false
% 1.45/1.00  --bc_imp_inh                            [conj_cone]
% 1.45/1.00  --conj_cone_tolerance                   3.
% 1.45/1.00  --extra_neg_conj                        none
% 1.45/1.00  --large_theory_mode                     true
% 1.45/1.00  --prolific_symb_bound                   200
% 1.45/1.00  --lt_threshold                          2000
% 1.45/1.00  --clause_weak_htbl                      true
% 1.45/1.00  --gc_record_bc_elim                     false
% 1.45/1.00  
% 1.45/1.00  ------ Preprocessing Options
% 1.45/1.00  
% 1.45/1.00  --preprocessing_flag                    true
% 1.45/1.00  --time_out_prep_mult                    0.1
% 1.45/1.00  --splitting_mode                        input
% 1.45/1.00  --splitting_grd                         true
% 1.45/1.00  --splitting_cvd                         false
% 1.45/1.00  --splitting_cvd_svl                     false
% 1.45/1.00  --splitting_nvd                         32
% 1.45/1.00  --sub_typing                            true
% 1.45/1.00  --prep_gs_sim                           true
% 1.45/1.00  --prep_unflatten                        true
% 1.45/1.00  --prep_res_sim                          true
% 1.45/1.00  --prep_upred                            true
% 1.45/1.00  --prep_sem_filter                       exhaustive
% 1.45/1.00  --prep_sem_filter_out                   false
% 1.45/1.00  --pred_elim                             true
% 1.45/1.00  --res_sim_input                         true
% 1.45/1.00  --eq_ax_congr_red                       true
% 1.45/1.00  --pure_diseq_elim                       true
% 1.45/1.00  --brand_transform                       false
% 1.45/1.00  --non_eq_to_eq                          false
% 1.45/1.00  --prep_def_merge                        true
% 1.45/1.00  --prep_def_merge_prop_impl              false
% 1.45/1.00  --prep_def_merge_mbd                    true
% 1.45/1.00  --prep_def_merge_tr_red                 false
% 1.45/1.00  --prep_def_merge_tr_cl                  false
% 1.45/1.00  --smt_preprocessing                     true
% 1.45/1.00  --smt_ac_axioms                         fast
% 1.45/1.00  --preprocessed_out                      false
% 1.45/1.00  --preprocessed_stats                    false
% 1.45/1.00  
% 1.45/1.00  ------ Abstraction refinement Options
% 1.45/1.00  
% 1.45/1.00  --abstr_ref                             []
% 1.45/1.00  --abstr_ref_prep                        false
% 1.45/1.00  --abstr_ref_until_sat                   false
% 1.45/1.00  --abstr_ref_sig_restrict                funpre
% 1.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.45/1.00  --abstr_ref_under                       []
% 1.45/1.00  
% 1.45/1.00  ------ SAT Options
% 1.45/1.00  
% 1.45/1.00  --sat_mode                              false
% 1.45/1.00  --sat_fm_restart_options                ""
% 1.45/1.00  --sat_gr_def                            false
% 1.45/1.00  --sat_epr_types                         true
% 1.45/1.00  --sat_non_cyclic_types                  false
% 1.45/1.00  --sat_finite_models                     false
% 1.45/1.00  --sat_fm_lemmas                         false
% 1.45/1.00  --sat_fm_prep                           false
% 1.45/1.00  --sat_fm_uc_incr                        true
% 1.45/1.00  --sat_out_model                         small
% 1.45/1.00  --sat_out_clauses                       false
% 1.45/1.00  
% 1.45/1.00  ------ QBF Options
% 1.45/1.00  
% 1.45/1.00  --qbf_mode                              false
% 1.45/1.00  --qbf_elim_univ                         false
% 1.45/1.00  --qbf_dom_inst                          none
% 1.45/1.00  --qbf_dom_pre_inst                      false
% 1.45/1.00  --qbf_sk_in                             false
% 1.45/1.00  --qbf_pred_elim                         true
% 1.45/1.00  --qbf_split                             512
% 1.45/1.00  
% 1.45/1.00  ------ BMC1 Options
% 1.45/1.00  
% 1.45/1.00  --bmc1_incremental                      false
% 1.45/1.00  --bmc1_axioms                           reachable_all
% 1.45/1.00  --bmc1_min_bound                        0
% 1.45/1.00  --bmc1_max_bound                        -1
% 1.45/1.00  --bmc1_max_bound_default                -1
% 1.45/1.00  --bmc1_symbol_reachability              true
% 1.45/1.00  --bmc1_property_lemmas                  false
% 1.45/1.00  --bmc1_k_induction                      false
% 1.45/1.00  --bmc1_non_equiv_states                 false
% 1.45/1.00  --bmc1_deadlock                         false
% 1.45/1.00  --bmc1_ucm                              false
% 1.45/1.00  --bmc1_add_unsat_core                   none
% 1.45/1.00  --bmc1_unsat_core_children              false
% 1.45/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.45/1.00  --bmc1_out_stat                         full
% 1.45/1.00  --bmc1_ground_init                      false
% 1.45/1.00  --bmc1_pre_inst_next_state              false
% 1.45/1.00  --bmc1_pre_inst_state                   false
% 1.45/1.00  --bmc1_pre_inst_reach_state             false
% 1.45/1.00  --bmc1_out_unsat_core                   false
% 1.45/1.00  --bmc1_aig_witness_out                  false
% 1.45/1.00  --bmc1_verbose                          false
% 1.45/1.00  --bmc1_dump_clauses_tptp                false
% 1.45/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.45/1.00  --bmc1_dump_file                        -
% 1.45/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.45/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.45/1.00  --bmc1_ucm_extend_mode                  1
% 1.45/1.00  --bmc1_ucm_init_mode                    2
% 1.45/1.00  --bmc1_ucm_cone_mode                    none
% 1.45/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.45/1.00  --bmc1_ucm_relax_model                  4
% 1.45/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.45/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.45/1.00  --bmc1_ucm_layered_model                none
% 1.45/1.00  --bmc1_ucm_max_lemma_size               10
% 1.45/1.00  
% 1.45/1.00  ------ AIG Options
% 1.45/1.00  
% 1.45/1.00  --aig_mode                              false
% 1.45/1.00  
% 1.45/1.00  ------ Instantiation Options
% 1.45/1.00  
% 1.45/1.00  --instantiation_flag                    true
% 1.45/1.00  --inst_sos_flag                         false
% 1.45/1.00  --inst_sos_phase                        true
% 1.45/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.45/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.45/1.00  --inst_lit_sel_side                     none
% 1.45/1.00  --inst_solver_per_active                1400
% 1.45/1.00  --inst_solver_calls_frac                1.
% 1.45/1.00  --inst_passive_queue_type               priority_queues
% 1.45/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.45/1.00  --inst_passive_queues_freq              [25;2]
% 1.45/1.00  --inst_dismatching                      true
% 1.45/1.00  --inst_eager_unprocessed_to_passive     true
% 1.45/1.00  --inst_prop_sim_given                   true
% 1.45/1.00  --inst_prop_sim_new                     false
% 1.45/1.00  --inst_subs_new                         false
% 1.45/1.00  --inst_eq_res_simp                      false
% 1.45/1.00  --inst_subs_given                       false
% 1.45/1.00  --inst_orphan_elimination               true
% 1.45/1.00  --inst_learning_loop_flag               true
% 1.45/1.00  --inst_learning_start                   3000
% 1.45/1.00  --inst_learning_factor                  2
% 1.45/1.00  --inst_start_prop_sim_after_learn       3
% 1.45/1.00  --inst_sel_renew                        solver
% 1.45/1.00  --inst_lit_activity_flag                true
% 1.45/1.00  --inst_restr_to_given                   false
% 1.45/1.00  --inst_activity_threshold               500
% 1.45/1.00  --inst_out_proof                        true
% 1.45/1.00  
% 1.45/1.00  ------ Resolution Options
% 1.45/1.00  
% 1.45/1.00  --resolution_flag                       false
% 1.45/1.00  --res_lit_sel                           adaptive
% 1.45/1.00  --res_lit_sel_side                      none
% 1.45/1.00  --res_ordering                          kbo
% 1.45/1.00  --res_to_prop_solver                    active
% 1.45/1.00  --res_prop_simpl_new                    false
% 1.45/1.00  --res_prop_simpl_given                  true
% 1.45/1.00  --res_passive_queue_type                priority_queues
% 1.45/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.45/1.00  --res_passive_queues_freq               [15;5]
% 1.45/1.00  --res_forward_subs                      full
% 1.45/1.00  --res_backward_subs                     full
% 1.45/1.00  --res_forward_subs_resolution           true
% 1.45/1.00  --res_backward_subs_resolution          true
% 1.45/1.00  --res_orphan_elimination                true
% 1.45/1.00  --res_time_limit                        2.
% 1.45/1.00  --res_out_proof                         true
% 1.45/1.00  
% 1.45/1.00  ------ Superposition Options
% 1.45/1.00  
% 1.45/1.00  --superposition_flag                    true
% 1.45/1.00  --sup_passive_queue_type                priority_queues
% 1.45/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.45/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.45/1.00  --demod_completeness_check              fast
% 1.45/1.00  --demod_use_ground                      true
% 1.45/1.00  --sup_to_prop_solver                    passive
% 1.45/1.00  --sup_prop_simpl_new                    true
% 1.45/1.00  --sup_prop_simpl_given                  true
% 1.45/1.00  --sup_fun_splitting                     false
% 1.45/1.00  --sup_smt_interval                      50000
% 1.45/1.00  
% 1.45/1.00  ------ Superposition Simplification Setup
% 1.45/1.00  
% 1.45/1.00  --sup_indices_passive                   []
% 1.45/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.45/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.00  --sup_full_bw                           [BwDemod]
% 1.45/1.00  --sup_immed_triv                        [TrivRules]
% 1.45/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.45/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.00  --sup_immed_bw_main                     []
% 1.45/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.45/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/1.00  
% 1.45/1.00  ------ Combination Options
% 1.45/1.00  
% 1.45/1.00  --comb_res_mult                         3
% 1.45/1.00  --comb_sup_mult                         2
% 1.45/1.00  --comb_inst_mult                        10
% 1.45/1.00  
% 1.45/1.00  ------ Debug Options
% 1.45/1.00  
% 1.45/1.00  --dbg_backtrace                         false
% 1.45/1.00  --dbg_dump_prop_clauses                 false
% 1.45/1.00  --dbg_dump_prop_clauses_file            -
% 1.45/1.00  --dbg_out_stat                          false
% 1.45/1.00  
% 1.45/1.00  
% 1.45/1.00  
% 1.45/1.00  
% 1.45/1.00  ------ Proving...
% 1.45/1.00  
% 1.45/1.00  
% 1.45/1.00  % SZS status Theorem for theBenchmark.p
% 1.45/1.00  
% 1.45/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.45/1.00  
% 1.45/1.00  fof(f16,plain,(
% 1.45/1.00    ! [X3,X2,X1,X0,X4] : (sP0(X3,X2,X1,X0,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 1.45/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.45/1.00  
% 1.45/1.00  fof(f18,plain,(
% 1.45/1.00    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 1.45/1.00    inference(nnf_transformation,[],[f16])).
% 1.45/1.00  
% 1.45/1.00  fof(f19,plain,(
% 1.45/1.00    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 1.45/1.00    inference(flattening,[],[f18])).
% 1.45/1.00  
% 1.45/1.00  fof(f20,plain,(
% 1.45/1.00    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.45/1.00    inference(rectify,[],[f19])).
% 1.45/1.00  
% 1.45/1.00  fof(f21,plain,(
% 1.45/1.00    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4))) => (((sK1(X0,X1,X2,X3,X4) != X0 & sK1(X0,X1,X2,X3,X4) != X1 & sK1(X0,X1,X2,X3,X4) != X2 & sK1(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK1(X0,X1,X2,X3,X4),X4)) & (sK1(X0,X1,X2,X3,X4) = X0 | sK1(X0,X1,X2,X3,X4) = X1 | sK1(X0,X1,X2,X3,X4) = X2 | sK1(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK1(X0,X1,X2,X3,X4),X4))))),
% 1.45/1.00    introduced(choice_axiom,[])).
% 1.45/1.00  
% 1.45/1.00  fof(f22,plain,(
% 1.45/1.00    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (((sK1(X0,X1,X2,X3,X4) != X0 & sK1(X0,X1,X2,X3,X4) != X1 & sK1(X0,X1,X2,X3,X4) != X2 & sK1(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK1(X0,X1,X2,X3,X4),X4)) & (sK1(X0,X1,X2,X3,X4) = X0 | sK1(X0,X1,X2,X3,X4) = X1 | sK1(X0,X1,X2,X3,X4) = X2 | sK1(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK1(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 1.45/1.00  
% 1.45/1.00  fof(f30,plain,(
% 1.45/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4) | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.45/1.00    inference(cnf_transformation,[],[f22])).
% 1.45/1.00  
% 1.45/1.00  fof(f8,conjecture,(
% 1.45/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/1.00  
% 1.45/1.00  fof(f9,negated_conjecture,(
% 1.45/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.45/1.00    inference(negated_conjecture,[],[f8])).
% 1.45/1.00  
% 1.45/1.00  fof(f14,plain,(
% 1.45/1.00    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.45/1.00    inference(ennf_transformation,[],[f9])).
% 1.45/1.00  
% 1.45/1.00  fof(f15,plain,(
% 1.45/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.45/1.00    inference(flattening,[],[f14])).
% 1.45/1.00  
% 1.45/1.00  fof(f24,plain,(
% 1.45/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5))),
% 1.45/1.00    introduced(choice_axiom,[])).
% 1.45/1.00  
% 1.45/1.00  fof(f25,plain,(
% 1.45/1.00    k1_funct_1(sK5,sK4) != sK3 & r2_hidden(sK4,sK2) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3)))) & v1_funct_2(sK5,sK2,k1_tarski(sK3)) & v1_funct_1(sK5)),
% 1.45/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f15,f24])).
% 1.45/1.00  
% 1.45/1.00  fof(f45,plain,(
% 1.45/1.00    v1_funct_2(sK5,sK2,k1_tarski(sK3))),
% 1.45/1.00    inference(cnf_transformation,[],[f25])).
% 1.45/1.00  
% 1.45/1.00  fof(f2,axiom,(
% 1.45/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/1.00  
% 1.45/1.00  fof(f27,plain,(
% 1.45/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/1.00    inference(cnf_transformation,[],[f2])).
% 1.45/1.00  
% 1.45/1.00  fof(f3,axiom,(
% 1.45/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/1.00  
% 1.45/1.00  fof(f28,plain,(
% 1.45/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.45/1.00    inference(cnf_transformation,[],[f3])).
% 1.45/1.00  
% 1.45/1.00  fof(f4,axiom,(
% 1.45/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/1.00  
% 1.45/1.00  fof(f29,plain,(
% 1.45/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.45/1.00    inference(cnf_transformation,[],[f4])).
% 1.45/1.00  
% 1.45/1.00  fof(f49,plain,(
% 1.45/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.45/1.00    inference(definition_unfolding,[],[f28,f29])).
% 1.45/1.00  
% 1.45/1.00  fof(f50,plain,(
% 1.45/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.45/1.00    inference(definition_unfolding,[],[f27,f49])).
% 1.45/1.00  
% 1.45/1.00  fof(f52,plain,(
% 1.45/1.00    v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.45/1.00    inference(definition_unfolding,[],[f45,f50])).
% 1.45/1.00  
% 1.45/1.00  fof(f7,axiom,(
% 1.45/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/1.00  
% 1.45/1.00  fof(f12,plain,(
% 1.45/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.45/1.00    inference(ennf_transformation,[],[f7])).
% 1.45/1.00  
% 1.45/1.00  fof(f13,plain,(
% 1.45/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.45/1.00    inference(flattening,[],[f12])).
% 1.45/1.00  
% 1.45/1.00  fof(f43,plain,(
% 1.45/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.45/1.00    inference(cnf_transformation,[],[f13])).
% 1.45/1.00  
% 1.45/1.00  fof(f46,plain,(
% 1.45/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 1.45/1.00    inference(cnf_transformation,[],[f25])).
% 1.45/1.00  
% 1.45/1.00  fof(f51,plain,(
% 1.45/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))))),
% 1.45/1.00    inference(definition_unfolding,[],[f46,f50])).
% 1.45/1.00  
% 1.45/1.00  fof(f44,plain,(
% 1.45/1.00    v1_funct_1(sK5)),
% 1.45/1.00    inference(cnf_transformation,[],[f25])).
% 1.45/1.00  
% 1.45/1.00  fof(f31,plain,(
% 1.45/1.00    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | ~sP0(X0,X1,X2,X3,X4)) )),
% 1.45/1.00    inference(cnf_transformation,[],[f22])).
% 1.45/1.00  
% 1.45/1.00  fof(f56,plain,(
% 1.45/1.00    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,X4) | ~sP0(X0,X1,X2,X6,X4)) )),
% 1.45/1.00    inference(equality_resolution,[],[f31])).
% 1.45/1.00  
% 1.45/1.00  fof(f5,axiom,(
% 1.45/1.00    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 1.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/1.00  
% 1.45/1.00  fof(f10,plain,(
% 1.45/1.00    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 1.45/1.00    inference(ennf_transformation,[],[f5])).
% 1.45/1.00  
% 1.45/1.00  fof(f17,plain,(
% 1.45/1.00    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP0(X3,X2,X1,X0,X4))),
% 1.45/1.00    inference(definition_folding,[],[f10,f16])).
% 1.45/1.00  
% 1.45/1.00  fof(f23,plain,(
% 1.45/1.00    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP0(X3,X2,X1,X0,X4)) & (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.45/1.00    inference(nnf_transformation,[],[f17])).
% 1.45/1.00  
% 1.45/1.00  fof(f40,plain,(
% 1.45/1.00    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 1.45/1.00    inference(cnf_transformation,[],[f23])).
% 1.45/1.00  
% 1.45/1.00  fof(f57,plain,(
% 1.45/1.00    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3))) )),
% 1.45/1.00    inference(equality_resolution,[],[f40])).
% 1.45/1.00  
% 1.45/1.00  fof(f1,axiom,(
% 1.45/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/1.00  
% 1.45/1.00  fof(f26,plain,(
% 1.45/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.45/1.00    inference(cnf_transformation,[],[f1])).
% 1.45/1.00  
% 1.45/1.00  fof(f6,axiom,(
% 1.45/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.45/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/1.00  
% 1.45/1.00  fof(f11,plain,(
% 1.45/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.45/1.00    inference(ennf_transformation,[],[f6])).
% 1.45/1.00  
% 1.45/1.00  fof(f42,plain,(
% 1.45/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.45/1.00    inference(cnf_transformation,[],[f11])).
% 1.45/1.00  
% 1.45/1.00  fof(f48,plain,(
% 1.45/1.00    k1_funct_1(sK5,sK4) != sK3),
% 1.45/1.00    inference(cnf_transformation,[],[f25])).
% 1.45/1.00  
% 1.45/1.00  fof(f47,plain,(
% 1.45/1.00    r2_hidden(sK4,sK2)),
% 1.45/1.00    inference(cnf_transformation,[],[f25])).
% 1.45/1.00  
% 1.45/1.00  cnf(c_1721,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.45/1.00      theory(equality) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_2140,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,X1)
% 1.45/1.00      | r2_hidden(X2,k1_xboole_0)
% 1.45/1.00      | X2 != X0
% 1.45/1.00      | k1_xboole_0 != X1 ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_1721]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_3079,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
% 1.45/1.00      | r2_hidden(X1,k1_xboole_0)
% 1.45/1.00      | X1 != X0
% 1.45/1.00      | k1_xboole_0 != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_2140]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_3081,plain,
% 1.45/1.00      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
% 1.45/1.00      | r2_hidden(sK3,k1_xboole_0)
% 1.45/1.00      | sK3 != sK3
% 1.45/1.00      | k1_xboole_0 != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_3079]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_10,plain,
% 1.45/1.00      ( ~ sP0(X0,X1,X2,X3,X4)
% 1.45/1.00      | ~ r2_hidden(X5,X4)
% 1.45/1.00      | X5 = X3
% 1.45/1.00      | X5 = X2
% 1.45/1.00      | X5 = X1
% 1.45/1.00      | X5 = X0 ),
% 1.45/1.00      inference(cnf_transformation,[],[f30]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_2150,plain,
% 1.45/1.00      ( ~ sP0(X0,X1,X2,sK3,X3)
% 1.45/1.00      | ~ r2_hidden(k1_funct_1(sK5,sK4),X3)
% 1.45/1.00      | k1_funct_1(sK5,sK4) = X0
% 1.45/1.00      | k1_funct_1(sK5,sK4) = X2
% 1.45/1.00      | k1_funct_1(sK5,sK4) = X1
% 1.45/1.00      | k1_funct_1(sK5,sK4) = sK3 ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_2501,plain,
% 1.45/1.00      ( ~ sP0(X0,X1,X2,sK3,k2_enumset1(sK3,X2,X1,X0))
% 1.45/1.00      | ~ r2_hidden(k1_funct_1(sK5,sK4),k2_enumset1(sK3,X2,X1,X0))
% 1.45/1.00      | k1_funct_1(sK5,sK4) = X0
% 1.45/1.00      | k1_funct_1(sK5,sK4) = X2
% 1.45/1.00      | k1_funct_1(sK5,sK4) = X1
% 1.45/1.00      | k1_funct_1(sK5,sK4) = sK3 ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_2150]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_2504,plain,
% 1.45/1.00      ( ~ sP0(sK3,sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3))
% 1.45/1.00      | ~ r2_hidden(k1_funct_1(sK5,sK4),k2_enumset1(sK3,sK3,sK3,sK3))
% 1.45/1.00      | k1_funct_1(sK5,sK4) = sK3 ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_2501]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_18,negated_conjecture,
% 1.45/1.00      ( v1_funct_2(sK5,sK2,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 1.45/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_14,plain,
% 1.45/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.45/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/1.00      | ~ r2_hidden(X3,X1)
% 1.45/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.45/1.00      | ~ v1_funct_1(X0)
% 1.45/1.00      | k1_xboole_0 = X2 ),
% 1.45/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_17,negated_conjecture,
% 1.45/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))) ),
% 1.45/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_220,plain,
% 1.45/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.45/1.00      | ~ r2_hidden(X3,X1)
% 1.45/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.45/1.00      | ~ v1_funct_1(X0)
% 1.45/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.45/1.00      | sK5 != X0
% 1.45/1.00      | k1_xboole_0 = X2 ),
% 1.45/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_221,plain,
% 1.45/1.00      ( ~ v1_funct_2(sK5,X0,X1)
% 1.45/1.00      | ~ r2_hidden(X2,X0)
% 1.45/1.00      | r2_hidden(k1_funct_1(sK5,X2),X1)
% 1.45/1.00      | ~ v1_funct_1(sK5)
% 1.45/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.45/1.00      | k1_xboole_0 = X1 ),
% 1.45/1.00      inference(unflattening,[status(thm)],[c_220]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_19,negated_conjecture,
% 1.45/1.00      ( v1_funct_1(sK5) ),
% 1.45/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_225,plain,
% 1.45/1.00      ( r2_hidden(k1_funct_1(sK5,X2),X1)
% 1.45/1.00      | ~ r2_hidden(X2,X0)
% 1.45/1.00      | ~ v1_funct_2(sK5,X0,X1)
% 1.45/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.45/1.00      | k1_xboole_0 = X1 ),
% 1.45/1.00      inference(global_propositional_subsumption,
% 1.45/1.00                [status(thm)],
% 1.45/1.00                [c_221,c_19]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_226,plain,
% 1.45/1.00      ( ~ v1_funct_2(sK5,X0,X1)
% 1.45/1.00      | ~ r2_hidden(X2,X0)
% 1.45/1.00      | r2_hidden(k1_funct_1(sK5,X2),X1)
% 1.45/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.45/1.00      | k1_xboole_0 = X1 ),
% 1.45/1.00      inference(renaming,[status(thm)],[c_225]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_253,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,X1)
% 1.45/1.00      | r2_hidden(k1_funct_1(sK5,X0),X2)
% 1.45/1.00      | k2_enumset1(sK3,sK3,sK3,sK3) != X2
% 1.45/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.45/1.00      | sK2 != X1
% 1.45/1.00      | sK5 != sK5
% 1.45/1.00      | k1_xboole_0 = X2 ),
% 1.45/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_226]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_254,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,sK2)
% 1.45/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_enumset1(sK3,sK3,sK3,sK3))
% 1.45/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) != k1_zfmisc_1(k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
% 1.45/1.00      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 1.45/1.00      inference(unflattening,[status(thm)],[c_253]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_967,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,sK2)
% 1.45/1.00      | r2_hidden(k1_funct_1(sK5,X0),k2_enumset1(sK3,sK3,sK3,sK3))
% 1.45/1.00      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 1.45/1.00      inference(equality_resolution_simp,[status(thm)],[c_254]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_2105,plain,
% 1.45/1.00      ( r2_hidden(k1_funct_1(sK5,sK4),k2_enumset1(sK3,sK3,sK3,sK3))
% 1.45/1.00      | ~ r2_hidden(sK4,sK2)
% 1.45/1.00      | k1_xboole_0 = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_967]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_9,plain,
% 1.45/1.00      ( ~ sP0(X0,X1,X2,X3,X4) | r2_hidden(X3,X4) ),
% 1.45/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_12,plain,
% 1.45/1.00      ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
% 1.45/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_785,plain,
% 1.45/1.00      ( r2_hidden(X0,X1)
% 1.45/1.00      | X2 != X3
% 1.45/1.00      | X4 != X0
% 1.45/1.00      | X5 != X6
% 1.45/1.00      | X7 != X8
% 1.45/1.00      | k2_enumset1(X4,X5,X7,X2) != X1 ),
% 1.45/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_786,plain,
% 1.45/1.00      ( r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
% 1.45/1.00      inference(unflattening,[status(thm)],[c_785]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_788,plain,
% 1.45/1.00      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_786]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_764,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,X1)
% 1.45/1.00      | X2 != X3
% 1.45/1.00      | X4 != X5
% 1.45/1.00      | X6 != X7
% 1.45/1.00      | X8 != X9
% 1.45/1.00      | X0 = X3
% 1.45/1.00      | X0 = X5
% 1.45/1.00      | X0 = X7
% 1.45/1.00      | X0 = X9
% 1.45/1.00      | k2_enumset1(X2,X4,X6,X8) != X1 ),
% 1.45/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_765,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
% 1.45/1.00      | X0 = X2
% 1.45/1.00      | X0 = X1
% 1.45/1.00      | X0 = X3
% 1.45/1.00      | X0 = X4 ),
% 1.45/1.00      inference(unflattening,[status(thm)],[c_764]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_767,plain,
% 1.45/1.00      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_765]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_0,plain,
% 1.45/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 1.45/1.00      inference(cnf_transformation,[],[f26]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_13,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.45/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_209,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.45/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_13]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_210,plain,
% 1.45/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.45/1.00      inference(unflattening,[status(thm)],[c_209]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_212,plain,
% 1.45/1.00      ( ~ r2_hidden(sK3,k1_xboole_0) ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_210]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_31,plain,
% 1.45/1.00      ( sP0(sK3,sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 1.45/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_15,negated_conjecture,
% 1.45/1.00      ( k1_funct_1(sK5,sK4) != sK3 ),
% 1.45/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(c_16,negated_conjecture,
% 1.45/1.00      ( r2_hidden(sK4,sK2) ),
% 1.45/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.45/1.00  
% 1.45/1.00  cnf(contradiction,plain,
% 1.45/1.00      ( $false ),
% 1.45/1.00      inference(minisat,
% 1.45/1.00                [status(thm)],
% 1.45/1.00                [c_3081,c_2504,c_2105,c_788,c_767,c_212,c_31,c_15,c_16]) ).
% 1.45/1.00  
% 1.45/1.00  
% 1.45/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.45/1.00  
% 1.45/1.00  ------                               Statistics
% 1.45/1.00  
% 1.45/1.00  ------ General
% 1.45/1.00  
% 1.45/1.00  abstr_ref_over_cycles:                  0
% 1.45/1.00  abstr_ref_under_cycles:                 0
% 1.45/1.00  gc_basic_clause_elim:                   0
% 1.45/1.00  forced_gc_time:                         0
% 1.45/1.00  parsing_time:                           0.011
% 1.45/1.00  unif_index_cands_time:                  0.
% 1.45/1.00  unif_index_add_time:                    0.
% 1.45/1.00  orderings_time:                         0.
% 1.45/1.00  out_proof_time:                         0.007
% 1.45/1.00  total_time:                             0.101
% 1.45/1.00  num_of_symbols:                         47
% 1.45/1.00  num_of_terms:                           1746
% 1.45/1.00  
% 1.45/1.00  ------ Preprocessing
% 1.45/1.00  
% 1.45/1.00  num_of_splits:                          0
% 1.45/1.00  num_of_split_atoms:                     0
% 1.45/1.00  num_of_reused_defs:                     0
% 1.45/1.00  num_eq_ax_congr_red:                    28
% 1.45/1.00  num_of_sem_filtered_clauses:            1
% 1.45/1.00  num_of_subtypes:                        0
% 1.45/1.00  monotx_restored_types:                  0
% 1.45/1.00  sat_num_of_epr_types:                   0
% 1.45/1.00  sat_num_of_non_cyclic_types:            0
% 1.45/1.00  sat_guarded_non_collapsed_types:        0
% 1.45/1.00  num_pure_diseq_elim:                    0
% 1.45/1.00  simp_replaced_by:                       0
% 1.45/1.00  res_preprocessed:                       81
% 1.45/1.00  prep_upred:                             0
% 1.45/1.00  prep_unflattend:                        65
% 1.45/1.00  smt_new_axioms:                         0
% 1.45/1.00  pred_elim_cands:                        2
% 1.45/1.00  pred_elim:                              4
% 1.45/1.00  pred_elim_cl:                           4
% 1.45/1.00  pred_elim_cycles:                       6
% 1.45/1.00  merged_defs:                            0
% 1.45/1.00  merged_defs_ncl:                        0
% 1.45/1.00  bin_hyper_res:                          0
% 1.45/1.00  prep_cycles:                            4
% 1.45/1.00  pred_elim_time:                         0.018
% 1.45/1.00  splitting_time:                         0.
% 1.45/1.00  sem_filter_time:                        0.
% 1.45/1.00  monotx_time:                            0.001
% 1.45/1.00  subtype_inf_time:                       0.
% 1.45/1.00  
% 1.45/1.00  ------ Problem properties
% 1.45/1.00  
% 1.45/1.00  clauses:                                16
% 1.45/1.00  conjectures:                            2
% 1.45/1.00  epr:                                    7
% 1.45/1.00  horn:                                   13
% 1.45/1.00  ground:                                 2
% 1.45/1.00  unary:                                  4
% 1.45/1.00  binary:                                 5
% 1.45/1.00  lits:                                   41
% 1.45/1.00  lits_eq:                                15
% 1.45/1.00  fd_pure:                                0
% 1.45/1.00  fd_pseudo:                              0
% 1.45/1.00  fd_cond:                                0
% 1.45/1.00  fd_pseudo_cond:                         2
% 1.45/1.00  ac_symbols:                             0
% 1.45/1.00  
% 1.45/1.00  ------ Propositional Solver
% 1.45/1.00  
% 1.45/1.00  prop_solver_calls:                      25
% 1.45/1.00  prop_fast_solver_calls:                 756
% 1.45/1.00  smt_solver_calls:                       0
% 1.45/1.00  smt_fast_solver_calls:                  0
% 1.45/1.00  prop_num_of_clauses:                    608
% 1.45/1.00  prop_preprocess_simplified:             3541
% 1.45/1.00  prop_fo_subsumed:                       1
% 1.45/1.00  prop_solver_time:                       0.
% 1.45/1.00  smt_solver_time:                        0.
% 1.45/1.00  smt_fast_solver_time:                   0.
% 1.45/1.00  prop_fast_solver_time:                  0.
% 1.45/1.00  prop_unsat_core_time:                   0.
% 1.45/1.00  
% 1.45/1.00  ------ QBF
% 1.45/1.00  
% 1.45/1.00  qbf_q_res:                              0
% 1.45/1.00  qbf_num_tautologies:                    0
% 1.45/1.00  qbf_prep_cycles:                        0
% 1.45/1.00  
% 1.45/1.00  ------ BMC1
% 1.45/1.00  
% 1.45/1.00  bmc1_current_bound:                     -1
% 1.45/1.00  bmc1_last_solved_bound:                 -1
% 1.45/1.00  bmc1_unsat_core_size:                   -1
% 1.45/1.00  bmc1_unsat_core_parents_size:           -1
% 1.45/1.00  bmc1_merge_next_fun:                    0
% 1.45/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.45/1.00  
% 1.45/1.00  ------ Instantiation
% 1.45/1.00  
% 1.45/1.00  inst_num_of_clauses:                    165
% 1.45/1.00  inst_num_in_passive:                    0
% 1.45/1.00  inst_num_in_active:                     93
% 1.45/1.00  inst_num_in_unprocessed:                71
% 1.45/1.00  inst_num_of_loops:                      110
% 1.45/1.00  inst_num_of_learning_restarts:          0
% 1.45/1.00  inst_num_moves_active_passive:          15
% 1.45/1.00  inst_lit_activity:                      0
% 1.45/1.00  inst_lit_activity_moves:                0
% 1.45/1.00  inst_num_tautologies:                   0
% 1.45/1.00  inst_num_prop_implied:                  0
% 1.45/1.00  inst_num_existing_simplified:           0
% 1.45/1.00  inst_num_eq_res_simplified:             0
% 1.45/1.00  inst_num_child_elim:                    0
% 1.45/1.00  inst_num_of_dismatching_blockings:      4
% 1.45/1.00  inst_num_of_non_proper_insts:           130
% 1.45/1.00  inst_num_of_duplicates:                 0
% 1.45/1.00  inst_inst_num_from_inst_to_res:         0
% 1.45/1.00  inst_dismatching_checking_time:         0.
% 1.45/1.00  
% 1.45/1.00  ------ Resolution
% 1.45/1.00  
% 1.45/1.00  res_num_of_clauses:                     0
% 1.45/1.00  res_num_in_passive:                     0
% 1.45/1.00  res_num_in_active:                      0
% 1.45/1.00  res_num_of_loops:                       85
% 1.45/1.00  res_forward_subset_subsumed:            53
% 1.45/1.00  res_backward_subset_subsumed:           0
% 1.45/1.00  res_forward_subsumed:                   0
% 1.45/1.00  res_backward_subsumed:                  0
% 1.45/1.00  res_forward_subsumption_resolution:     0
% 1.45/1.00  res_backward_subsumption_resolution:    0
% 1.45/1.00  res_clause_to_clause_subsumption:       671
% 1.45/1.00  res_orphan_elimination:                 0
% 1.45/1.00  res_tautology_del:                      6
% 1.45/1.00  res_num_eq_res_simplified:              1
% 1.45/1.00  res_num_sel_changes:                    0
% 1.45/1.00  res_moves_from_active_to_pass:          0
% 1.45/1.00  
% 1.45/1.00  ------ Superposition
% 1.45/1.00  
% 1.45/1.00  sup_time_total:                         0.
% 1.45/1.00  sup_time_generating:                    0.
% 1.45/1.00  sup_time_sim_full:                      0.
% 1.45/1.00  sup_time_sim_immed:                     0.
% 1.45/1.00  
% 1.45/1.00  sup_num_of_clauses:                     23
% 1.45/1.00  sup_num_in_active:                      20
% 1.45/1.00  sup_num_in_passive:                     3
% 1.45/1.00  sup_num_of_loops:                       20
% 1.45/1.00  sup_fw_superposition:                   11
% 1.45/1.00  sup_bw_superposition:                   0
% 1.45/1.00  sup_immediate_simplified:               0
% 1.45/1.00  sup_given_eliminated:                   0
% 1.45/1.00  comparisons_done:                       0
% 1.45/1.00  comparisons_avoided:                    0
% 1.45/1.00  
% 1.45/1.00  ------ Simplifications
% 1.45/1.00  
% 1.45/1.00  
% 1.45/1.00  sim_fw_subset_subsumed:                 0
% 1.45/1.00  sim_bw_subset_subsumed:                 0
% 1.45/1.00  sim_fw_subsumed:                        0
% 1.45/1.00  sim_bw_subsumed:                        0
% 1.45/1.00  sim_fw_subsumption_res:                 0
% 1.45/1.00  sim_bw_subsumption_res:                 0
% 1.45/1.00  sim_tautology_del:                      0
% 1.45/1.00  sim_eq_tautology_del:                   4
% 1.45/1.00  sim_eq_res_simp:                        0
% 1.45/1.00  sim_fw_demodulated:                     0
% 1.45/1.00  sim_bw_demodulated:                     0
% 1.45/1.00  sim_light_normalised:                   0
% 1.45/1.00  sim_joinable_taut:                      0
% 1.45/1.00  sim_joinable_simp:                      0
% 1.45/1.00  sim_ac_normalised:                      0
% 1.45/1.00  sim_smt_subsumption:                    0
% 1.45/1.00  
%------------------------------------------------------------------------------
