%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0393+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:11 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 162 expanded)
%              Number of clauses        :   54 (  64 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  354 ( 854 expanded)
%              Number of equality atoms :  164 ( 384 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f49])).

fof(f72,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f71])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK2(X0,X5))
        & r2_hidden(sK2(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(X2,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK0(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK0(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK0(X0,X1),sK1(X0,X1))
                  & r2_hidden(sK1(X0,X1),X0) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK0(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK2(X0,X5))
                    & r2_hidden(sK2(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK0(X0,X1),sK1(X0,X1))
      | ~ r2_hidden(sK0(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK1(X0,X1),X0)
      | ~ r2_hidden(sK0(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f10,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f10])).

fof(f17,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f35])).

fof(f61,plain,(
    k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_439,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1803,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k1_tarski(sK5),X2),X2)
    | X1 != X2
    | X0 != sK0(k1_tarski(sK5),X2) ),
    inference(instantiation,[status(thm)],[c_439])).

cnf(c_4107,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK5),X0),X0)
    | r2_hidden(sK0(k1_tarski(sK5),X0),X1)
    | X1 != X0
    | sK0(k1_tarski(sK5),X0) != sK0(k1_tarski(sK5),X0) ),
    inference(instantiation,[status(thm)],[c_1803])).

cnf(c_11629,plain,
    ( r2_hidden(sK0(k1_tarski(sK5),sK5),X0)
    | ~ r2_hidden(sK0(k1_tarski(sK5),sK5),sK5)
    | X0 != sK5
    | sK0(k1_tarski(sK5),sK5) != sK0(k1_tarski(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_4107])).

cnf(c_15792,plain,
    ( r2_hidden(sK0(k1_tarski(sK5),sK5),sK1(k1_tarski(sK5),sK5))
    | ~ r2_hidden(sK0(k1_tarski(sK5),sK5),sK5)
    | sK1(k1_tarski(sK5),sK5) != sK5
    | sK0(k1_tarski(sK5),sK5) != sK0(k1_tarski(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_11629])).

cnf(c_436,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2931,plain,
    ( X0 != X1
    | o_0_0_xboole_0 != X1
    | o_0_0_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_6542,plain,
    ( X0 != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2931])).

cnf(c_6543,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | o_0_0_xboole_0 = k1_xboole_0
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6542])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1755,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK5))
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4610,plain,
    ( ~ r2_hidden(sK1(k1_tarski(sK5),sK5),k1_tarski(sK5))
    | sK1(k1_tarski(sK5),sK5) = sK5 ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_4611,plain,
    ( sK1(k1_tarski(sK5),sK5) = sK5
    | r2_hidden(sK1(k1_tarski(sK5),sK5),k1_tarski(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4610])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4283,plain,
    ( r2_hidden(sK0(k1_tarski(sK5),sK5),k1_tarski(sK0(k1_tarski(sK5),sK5))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_435,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3895,plain,
    ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_917,plain,
    ( X0 != X1
    | k1_tarski(sK5) != X1
    | k1_tarski(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_3754,plain,
    ( X0 != k1_tarski(sK5)
    | k1_tarski(sK5) = X0
    | k1_tarski(sK5) != k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_917])).

cnf(c_3755,plain,
    ( k1_tarski(sK5) != k1_tarski(sK5)
    | k1_tarski(sK5) = k1_xboole_0
    | k1_xboole_0 != k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_3754])).

cnf(c_1227,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK5),sK5),k1_tarski(X0))
    | sK0(k1_tarski(sK5),sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1976,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK5),sK5),k1_tarski(sK0(k1_tarski(sK5),sK5)))
    | sK0(k1_tarski(sK5),sK5) = sK0(k1_tarski(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_1227])).

cnf(c_437,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1127,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tarski(sK5),X2)
    | X2 != X1
    | k1_tarski(sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_1620,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tarski(sK5),o_0_0_xboole_0)
    | k1_tarski(sK5) != X0
    | o_0_0_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1622,plain,
    ( r1_tarski(k1_tarski(sK5),o_0_0_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_tarski(sK5) != k1_xboole_0
    | o_0_0_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_1089,plain,
    ( k1_tarski(sK5) = k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_18,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_179,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_180,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_223,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_22,c_180])).

cnf(c_304,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | o_0_0_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_223])).

cnf(c_305,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,o_0_0_xboole_0) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_1053,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | ~ r1_tarski(k1_tarski(sK5),o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_846,plain,
    ( r2_hidden(sK5,k1_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_847,plain,
    ( r2_hidden(sK5,k1_tarski(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X1,X2),X2)
    | r2_hidden(sK0(X1,X2),X0)
    | k1_setfam_1(X1) = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_751,plain,
    ( ~ r2_hidden(X0,k1_tarski(sK5))
    | r2_hidden(sK0(k1_tarski(sK5),sK5),X0)
    | r2_hidden(sK0(k1_tarski(sK5),sK5),sK5)
    | k1_setfam_1(k1_tarski(sK5)) = sK5
    | k1_xboole_0 = k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_799,plain,
    ( r2_hidden(sK0(k1_tarski(sK5),sK5),sK5)
    | ~ r2_hidden(sK5,k1_tarski(sK5))
    | k1_setfam_1(k1_tarski(sK5)) = sK5
    | k1_xboole_0 = k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_800,plain,
    ( k1_setfam_1(k1_tarski(sK5)) = sK5
    | k1_xboole_0 = k1_tarski(sK5)
    | r2_hidden(sK0(k1_tarski(sK5),sK5),sK5) = iProver_top
    | r2_hidden(sK5,k1_tarski(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),sK1(X0,X1))
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_745,plain,
    ( ~ r2_hidden(sK0(k1_tarski(sK5),sK5),sK1(k1_tarski(sK5),sK5))
    | ~ r2_hidden(sK0(k1_tarski(sK5),sK5),sK5)
    | k1_setfam_1(k1_tarski(sK5)) = sK5
    | k1_xboole_0 = k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | ~ r2_hidden(sK0(X0,X1),X1)
    | k1_setfam_1(X0) = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_746,plain,
    ( r2_hidden(sK1(k1_tarski(sK5),sK5),k1_tarski(sK5))
    | ~ r2_hidden(sK0(k1_tarski(sK5),sK5),sK5)
    | k1_setfam_1(k1_tarski(sK5)) = sK5
    | k1_xboole_0 = k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_747,plain,
    ( k1_setfam_1(k1_tarski(sK5)) = sK5
    | k1_xboole_0 = k1_tarski(sK5)
    | r2_hidden(sK1(k1_tarski(sK5),sK5),k1_tarski(sK5)) = iProver_top
    | r2_hidden(sK0(k1_tarski(sK5),sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_299,plain,
    ( o_0_0_xboole_0 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_300,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_77,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_24,negated_conjecture,
    ( k1_setfam_1(k1_tarski(sK5)) != sK5 ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15792,c_6543,c_4611,c_4283,c_3895,c_3755,c_1976,c_1622,c_1089,c_1053,c_847,c_846,c_800,c_799,c_745,c_747,c_300,c_77,c_24])).


%------------------------------------------------------------------------------
