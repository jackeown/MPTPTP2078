%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:48 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 110 expanded)
%              Number of clauses        :   27 (  29 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  343 ( 457 expanded)
%              Number of equality atoms :  220 ( 228 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   34 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ),
    inference(definition_folding,[],[f18,f24])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) )
      & ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f5])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
      | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(definition_unfolding,[],[f59,f40])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP0(X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(equality_resolution,[],[f76])).

fof(f26,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f27,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8
                & X6 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | X6 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9 ) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ( X0 != X8
              & X1 != X8
              & X2 != X8
              & X3 != X8
              & X4 != X8
              & X5 != X8
              & X6 != X8 )
            | ~ r2_hidden(X8,X7) )
          & ( X0 = X8
            | X1 = X8
            | X2 = X8
            | X3 = X8
            | X4 = X8
            | X5 = X8
            | X6 = X8
            | r2_hidden(X8,X7) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9 ) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | X0 != X9
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X6,X4,X2,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | ~ sP0(X9,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(equality_resolution,[],[f50])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,sK4))))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK3,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f34,f33,f32])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f72])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f61,f74])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_6937,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
    | r2_hidden(X0,X7) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_6946,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7) != iProver_top
    | r2_hidden(X0,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9278,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6937,c_6946])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6934,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6936,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7394,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) = k9_subset_1(u1_struct_0(sK2),X0,sK4) ),
    inference(superposition,[status(thm)],[c_6934,c_6936])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,plain,
    ( r1_tarski(k1_setfam_1(X0),X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_290,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X3
    | k1_setfam_1(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_21])).

cnf(c_291,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_6932,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_7719,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK4)) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK2),X1,sK4),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_6932])).

cnf(c_9589,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,sK4),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9278,c_7719])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(k1_pre_topc(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_6931,plain,
    ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_7178,plain,
    ( u1_struct_0(k1_pre_topc(sK2,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_6934,c_6931])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6935,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7211,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7178,c_6935])).

cnf(c_9612,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_9589,c_7211])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:48:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.00/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.02  
% 3.00/1.02  ------  iProver source info
% 3.00/1.02  
% 3.00/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.02  git: non_committed_changes: false
% 3.00/1.02  git: last_make_outside_of_git: false
% 3.00/1.02  
% 3.00/1.02  ------ 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options
% 3.00/1.02  
% 3.00/1.02  --out_options                           all
% 3.00/1.02  --tptp_safe_out                         true
% 3.00/1.02  --problem_path                          ""
% 3.00/1.02  --include_path                          ""
% 3.00/1.02  --clausifier                            res/vclausify_rel
% 3.00/1.02  --clausifier_options                    --mode clausify
% 3.00/1.02  --stdin                                 false
% 3.00/1.02  --stats_out                             all
% 3.00/1.02  
% 3.00/1.02  ------ General Options
% 3.00/1.02  
% 3.00/1.02  --fof                                   false
% 3.00/1.02  --time_out_real                         305.
% 3.00/1.02  --time_out_virtual                      -1.
% 3.00/1.02  --symbol_type_check                     false
% 3.00/1.02  --clausify_out                          false
% 3.00/1.02  --sig_cnt_out                           false
% 3.00/1.02  --trig_cnt_out                          false
% 3.00/1.02  --trig_cnt_out_tolerance                1.
% 3.00/1.02  --trig_cnt_out_sk_spl                   false
% 3.00/1.02  --abstr_cl_out                          false
% 3.00/1.02  
% 3.00/1.02  ------ Global Options
% 3.00/1.02  
% 3.00/1.02  --schedule                              default
% 3.00/1.02  --add_important_lit                     false
% 3.00/1.02  --prop_solver_per_cl                    1000
% 3.00/1.02  --min_unsat_core                        false
% 3.00/1.02  --soft_assumptions                      false
% 3.00/1.02  --soft_lemma_size                       3
% 3.00/1.02  --prop_impl_unit_size                   0
% 3.00/1.02  --prop_impl_unit                        []
% 3.00/1.02  --share_sel_clauses                     true
% 3.00/1.02  --reset_solvers                         false
% 3.00/1.02  --bc_imp_inh                            [conj_cone]
% 3.00/1.02  --conj_cone_tolerance                   3.
% 3.00/1.02  --extra_neg_conj                        none
% 3.00/1.02  --large_theory_mode                     true
% 3.00/1.02  --prolific_symb_bound                   200
% 3.00/1.02  --lt_threshold                          2000
% 3.00/1.02  --clause_weak_htbl                      true
% 3.00/1.02  --gc_record_bc_elim                     false
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing Options
% 3.00/1.02  
% 3.00/1.02  --preprocessing_flag                    true
% 3.00/1.02  --time_out_prep_mult                    0.1
% 3.00/1.02  --splitting_mode                        input
% 3.00/1.02  --splitting_grd                         true
% 3.00/1.02  --splitting_cvd                         false
% 3.00/1.02  --splitting_cvd_svl                     false
% 3.00/1.02  --splitting_nvd                         32
% 3.00/1.02  --sub_typing                            true
% 3.00/1.02  --prep_gs_sim                           true
% 3.00/1.02  --prep_unflatten                        true
% 3.00/1.02  --prep_res_sim                          true
% 3.00/1.02  --prep_upred                            true
% 3.00/1.02  --prep_sem_filter                       exhaustive
% 3.00/1.02  --prep_sem_filter_out                   false
% 3.00/1.02  --pred_elim                             true
% 3.00/1.02  --res_sim_input                         true
% 3.00/1.02  --eq_ax_congr_red                       true
% 3.00/1.02  --pure_diseq_elim                       true
% 3.00/1.02  --brand_transform                       false
% 3.00/1.02  --non_eq_to_eq                          false
% 3.00/1.02  --prep_def_merge                        true
% 3.00/1.02  --prep_def_merge_prop_impl              false
% 3.00/1.02  --prep_def_merge_mbd                    true
% 3.00/1.02  --prep_def_merge_tr_red                 false
% 3.00/1.02  --prep_def_merge_tr_cl                  false
% 3.00/1.02  --smt_preprocessing                     true
% 3.00/1.02  --smt_ac_axioms                         fast
% 3.00/1.02  --preprocessed_out                      false
% 3.00/1.02  --preprocessed_stats                    false
% 3.00/1.02  
% 3.00/1.02  ------ Abstraction refinement Options
% 3.00/1.02  
% 3.00/1.02  --abstr_ref                             []
% 3.00/1.02  --abstr_ref_prep                        false
% 3.00/1.02  --abstr_ref_until_sat                   false
% 3.00/1.02  --abstr_ref_sig_restrict                funpre
% 3.00/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.02  --abstr_ref_under                       []
% 3.00/1.02  
% 3.00/1.02  ------ SAT Options
% 3.00/1.02  
% 3.00/1.02  --sat_mode                              false
% 3.00/1.02  --sat_fm_restart_options                ""
% 3.00/1.02  --sat_gr_def                            false
% 3.00/1.02  --sat_epr_types                         true
% 3.00/1.02  --sat_non_cyclic_types                  false
% 3.00/1.02  --sat_finite_models                     false
% 3.00/1.02  --sat_fm_lemmas                         false
% 3.00/1.02  --sat_fm_prep                           false
% 3.00/1.02  --sat_fm_uc_incr                        true
% 3.00/1.02  --sat_out_model                         small
% 3.00/1.02  --sat_out_clauses                       false
% 3.00/1.02  
% 3.00/1.02  ------ QBF Options
% 3.00/1.02  
% 3.00/1.02  --qbf_mode                              false
% 3.00/1.02  --qbf_elim_univ                         false
% 3.00/1.02  --qbf_dom_inst                          none
% 3.00/1.02  --qbf_dom_pre_inst                      false
% 3.00/1.02  --qbf_sk_in                             false
% 3.00/1.02  --qbf_pred_elim                         true
% 3.00/1.02  --qbf_split                             512
% 3.00/1.02  
% 3.00/1.02  ------ BMC1 Options
% 3.00/1.02  
% 3.00/1.02  --bmc1_incremental                      false
% 3.00/1.02  --bmc1_axioms                           reachable_all
% 3.00/1.02  --bmc1_min_bound                        0
% 3.00/1.02  --bmc1_max_bound                        -1
% 3.00/1.02  --bmc1_max_bound_default                -1
% 3.00/1.02  --bmc1_symbol_reachability              true
% 3.00/1.02  --bmc1_property_lemmas                  false
% 3.00/1.02  --bmc1_k_induction                      false
% 3.00/1.02  --bmc1_non_equiv_states                 false
% 3.00/1.02  --bmc1_deadlock                         false
% 3.00/1.02  --bmc1_ucm                              false
% 3.00/1.02  --bmc1_add_unsat_core                   none
% 3.00/1.02  --bmc1_unsat_core_children              false
% 3.00/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.02  --bmc1_out_stat                         full
% 3.00/1.02  --bmc1_ground_init                      false
% 3.00/1.02  --bmc1_pre_inst_next_state              false
% 3.00/1.02  --bmc1_pre_inst_state                   false
% 3.00/1.02  --bmc1_pre_inst_reach_state             false
% 3.00/1.02  --bmc1_out_unsat_core                   false
% 3.00/1.02  --bmc1_aig_witness_out                  false
% 3.00/1.02  --bmc1_verbose                          false
% 3.00/1.02  --bmc1_dump_clauses_tptp                false
% 3.00/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.02  --bmc1_dump_file                        -
% 3.00/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.02  --bmc1_ucm_extend_mode                  1
% 3.00/1.02  --bmc1_ucm_init_mode                    2
% 3.00/1.02  --bmc1_ucm_cone_mode                    none
% 3.00/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.02  --bmc1_ucm_relax_model                  4
% 3.00/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.02  --bmc1_ucm_layered_model                none
% 3.00/1.02  --bmc1_ucm_max_lemma_size               10
% 3.00/1.02  
% 3.00/1.02  ------ AIG Options
% 3.00/1.02  
% 3.00/1.02  --aig_mode                              false
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation Options
% 3.00/1.02  
% 3.00/1.02  --instantiation_flag                    true
% 3.00/1.02  --inst_sos_flag                         false
% 3.00/1.02  --inst_sos_phase                        true
% 3.00/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel_side                     num_symb
% 3.00/1.02  --inst_solver_per_active                1400
% 3.00/1.02  --inst_solver_calls_frac                1.
% 3.00/1.02  --inst_passive_queue_type               priority_queues
% 3.00/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.02  --inst_passive_queues_freq              [25;2]
% 3.00/1.02  --inst_dismatching                      true
% 3.00/1.02  --inst_eager_unprocessed_to_passive     true
% 3.00/1.02  --inst_prop_sim_given                   true
% 3.00/1.02  --inst_prop_sim_new                     false
% 3.00/1.02  --inst_subs_new                         false
% 3.00/1.02  --inst_eq_res_simp                      false
% 3.00/1.02  --inst_subs_given                       false
% 3.00/1.02  --inst_orphan_elimination               true
% 3.00/1.02  --inst_learning_loop_flag               true
% 3.00/1.02  --inst_learning_start                   3000
% 3.00/1.02  --inst_learning_factor                  2
% 3.00/1.02  --inst_start_prop_sim_after_learn       3
% 3.00/1.02  --inst_sel_renew                        solver
% 3.00/1.02  --inst_lit_activity_flag                true
% 3.00/1.02  --inst_restr_to_given                   false
% 3.00/1.02  --inst_activity_threshold               500
% 3.00/1.02  --inst_out_proof                        true
% 3.00/1.02  
% 3.00/1.02  ------ Resolution Options
% 3.00/1.02  
% 3.00/1.02  --resolution_flag                       true
% 3.00/1.02  --res_lit_sel                           adaptive
% 3.00/1.02  --res_lit_sel_side                      none
% 3.00/1.02  --res_ordering                          kbo
% 3.00/1.02  --res_to_prop_solver                    active
% 3.00/1.02  --res_prop_simpl_new                    false
% 3.00/1.02  --res_prop_simpl_given                  true
% 3.00/1.02  --res_passive_queue_type                priority_queues
% 3.00/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.02  --res_passive_queues_freq               [15;5]
% 3.00/1.02  --res_forward_subs                      full
% 3.00/1.02  --res_backward_subs                     full
% 3.00/1.02  --res_forward_subs_resolution           true
% 3.00/1.02  --res_backward_subs_resolution          true
% 3.00/1.02  --res_orphan_elimination                true
% 3.00/1.02  --res_time_limit                        2.
% 3.00/1.02  --res_out_proof                         true
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Options
% 3.00/1.02  
% 3.00/1.02  --superposition_flag                    true
% 3.00/1.02  --sup_passive_queue_type                priority_queues
% 3.00/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.02  --demod_completeness_check              fast
% 3.00/1.02  --demod_use_ground                      true
% 3.00/1.02  --sup_to_prop_solver                    passive
% 3.00/1.02  --sup_prop_simpl_new                    true
% 3.00/1.02  --sup_prop_simpl_given                  true
% 3.00/1.02  --sup_fun_splitting                     false
% 3.00/1.02  --sup_smt_interval                      50000
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Simplification Setup
% 3.00/1.02  
% 3.00/1.02  --sup_indices_passive                   []
% 3.00/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_full_bw                           [BwDemod]
% 3.00/1.02  --sup_immed_triv                        [TrivRules]
% 3.00/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_immed_bw_main                     []
% 3.00/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  
% 3.00/1.02  ------ Combination Options
% 3.00/1.02  
% 3.00/1.02  --comb_res_mult                         3
% 3.00/1.02  --comb_sup_mult                         2
% 3.00/1.02  --comb_inst_mult                        10
% 3.00/1.02  
% 3.00/1.02  ------ Debug Options
% 3.00/1.02  
% 3.00/1.02  --dbg_backtrace                         false
% 3.00/1.02  --dbg_dump_prop_clauses                 false
% 3.00/1.02  --dbg_dump_prop_clauses_file            -
% 3.00/1.02  --dbg_out_stat                          false
% 3.00/1.02  ------ Parsing...
% 3.00/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.02  ------ Proving...
% 3.00/1.02  ------ Problem Properties 
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  clauses                                 25
% 3.00/1.02  conjectures                             3
% 3.00/1.02  EPR                                     8
% 3.00/1.02  Horn                                    23
% 3.00/1.02  unary                                   4
% 3.00/1.02  binary                                  12
% 3.00/1.02  lits                                    67
% 3.00/1.02  lits eq                                 25
% 3.00/1.02  fd_pure                                 0
% 3.00/1.02  fd_pseudo                               0
% 3.00/1.02  fd_cond                                 0
% 3.00/1.02  fd_pseudo_cond                          2
% 3.00/1.02  AC symbols                              0
% 3.00/1.02  
% 3.00/1.02  ------ Schedule dynamic 5 is on 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  ------ 
% 3.00/1.02  Current options:
% 3.00/1.02  ------ 
% 3.00/1.02  
% 3.00/1.02  ------ Input Options
% 3.00/1.02  
% 3.00/1.02  --out_options                           all
% 3.00/1.02  --tptp_safe_out                         true
% 3.00/1.02  --problem_path                          ""
% 3.00/1.02  --include_path                          ""
% 3.00/1.02  --clausifier                            res/vclausify_rel
% 3.00/1.02  --clausifier_options                    --mode clausify
% 3.00/1.02  --stdin                                 false
% 3.00/1.02  --stats_out                             all
% 3.00/1.02  
% 3.00/1.02  ------ General Options
% 3.00/1.02  
% 3.00/1.02  --fof                                   false
% 3.00/1.02  --time_out_real                         305.
% 3.00/1.02  --time_out_virtual                      -1.
% 3.00/1.02  --symbol_type_check                     false
% 3.00/1.02  --clausify_out                          false
% 3.00/1.02  --sig_cnt_out                           false
% 3.00/1.02  --trig_cnt_out                          false
% 3.00/1.02  --trig_cnt_out_tolerance                1.
% 3.00/1.02  --trig_cnt_out_sk_spl                   false
% 3.00/1.02  --abstr_cl_out                          false
% 3.00/1.02  
% 3.00/1.02  ------ Global Options
% 3.00/1.02  
% 3.00/1.02  --schedule                              default
% 3.00/1.02  --add_important_lit                     false
% 3.00/1.02  --prop_solver_per_cl                    1000
% 3.00/1.02  --min_unsat_core                        false
% 3.00/1.02  --soft_assumptions                      false
% 3.00/1.02  --soft_lemma_size                       3
% 3.00/1.02  --prop_impl_unit_size                   0
% 3.00/1.02  --prop_impl_unit                        []
% 3.00/1.02  --share_sel_clauses                     true
% 3.00/1.02  --reset_solvers                         false
% 3.00/1.02  --bc_imp_inh                            [conj_cone]
% 3.00/1.02  --conj_cone_tolerance                   3.
% 3.00/1.02  --extra_neg_conj                        none
% 3.00/1.02  --large_theory_mode                     true
% 3.00/1.02  --prolific_symb_bound                   200
% 3.00/1.02  --lt_threshold                          2000
% 3.00/1.02  --clause_weak_htbl                      true
% 3.00/1.02  --gc_record_bc_elim                     false
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing Options
% 3.00/1.02  
% 3.00/1.02  --preprocessing_flag                    true
% 3.00/1.02  --time_out_prep_mult                    0.1
% 3.00/1.02  --splitting_mode                        input
% 3.00/1.02  --splitting_grd                         true
% 3.00/1.02  --splitting_cvd                         false
% 3.00/1.02  --splitting_cvd_svl                     false
% 3.00/1.02  --splitting_nvd                         32
% 3.00/1.02  --sub_typing                            true
% 3.00/1.02  --prep_gs_sim                           true
% 3.00/1.02  --prep_unflatten                        true
% 3.00/1.02  --prep_res_sim                          true
% 3.00/1.02  --prep_upred                            true
% 3.00/1.02  --prep_sem_filter                       exhaustive
% 3.00/1.02  --prep_sem_filter_out                   false
% 3.00/1.02  --pred_elim                             true
% 3.00/1.02  --res_sim_input                         true
% 3.00/1.02  --eq_ax_congr_red                       true
% 3.00/1.02  --pure_diseq_elim                       true
% 3.00/1.02  --brand_transform                       false
% 3.00/1.02  --non_eq_to_eq                          false
% 3.00/1.02  --prep_def_merge                        true
% 3.00/1.02  --prep_def_merge_prop_impl              false
% 3.00/1.02  --prep_def_merge_mbd                    true
% 3.00/1.02  --prep_def_merge_tr_red                 false
% 3.00/1.02  --prep_def_merge_tr_cl                  false
% 3.00/1.02  --smt_preprocessing                     true
% 3.00/1.02  --smt_ac_axioms                         fast
% 3.00/1.02  --preprocessed_out                      false
% 3.00/1.02  --preprocessed_stats                    false
% 3.00/1.02  
% 3.00/1.02  ------ Abstraction refinement Options
% 3.00/1.02  
% 3.00/1.02  --abstr_ref                             []
% 3.00/1.02  --abstr_ref_prep                        false
% 3.00/1.02  --abstr_ref_until_sat                   false
% 3.00/1.02  --abstr_ref_sig_restrict                funpre
% 3.00/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.02  --abstr_ref_under                       []
% 3.00/1.02  
% 3.00/1.02  ------ SAT Options
% 3.00/1.02  
% 3.00/1.02  --sat_mode                              false
% 3.00/1.02  --sat_fm_restart_options                ""
% 3.00/1.02  --sat_gr_def                            false
% 3.00/1.02  --sat_epr_types                         true
% 3.00/1.02  --sat_non_cyclic_types                  false
% 3.00/1.02  --sat_finite_models                     false
% 3.00/1.02  --sat_fm_lemmas                         false
% 3.00/1.02  --sat_fm_prep                           false
% 3.00/1.02  --sat_fm_uc_incr                        true
% 3.00/1.02  --sat_out_model                         small
% 3.00/1.02  --sat_out_clauses                       false
% 3.00/1.02  
% 3.00/1.02  ------ QBF Options
% 3.00/1.02  
% 3.00/1.02  --qbf_mode                              false
% 3.00/1.02  --qbf_elim_univ                         false
% 3.00/1.02  --qbf_dom_inst                          none
% 3.00/1.02  --qbf_dom_pre_inst                      false
% 3.00/1.02  --qbf_sk_in                             false
% 3.00/1.02  --qbf_pred_elim                         true
% 3.00/1.02  --qbf_split                             512
% 3.00/1.02  
% 3.00/1.02  ------ BMC1 Options
% 3.00/1.02  
% 3.00/1.02  --bmc1_incremental                      false
% 3.00/1.02  --bmc1_axioms                           reachable_all
% 3.00/1.02  --bmc1_min_bound                        0
% 3.00/1.02  --bmc1_max_bound                        -1
% 3.00/1.02  --bmc1_max_bound_default                -1
% 3.00/1.02  --bmc1_symbol_reachability              true
% 3.00/1.02  --bmc1_property_lemmas                  false
% 3.00/1.02  --bmc1_k_induction                      false
% 3.00/1.02  --bmc1_non_equiv_states                 false
% 3.00/1.02  --bmc1_deadlock                         false
% 3.00/1.02  --bmc1_ucm                              false
% 3.00/1.02  --bmc1_add_unsat_core                   none
% 3.00/1.02  --bmc1_unsat_core_children              false
% 3.00/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.02  --bmc1_out_stat                         full
% 3.00/1.02  --bmc1_ground_init                      false
% 3.00/1.02  --bmc1_pre_inst_next_state              false
% 3.00/1.02  --bmc1_pre_inst_state                   false
% 3.00/1.02  --bmc1_pre_inst_reach_state             false
% 3.00/1.02  --bmc1_out_unsat_core                   false
% 3.00/1.02  --bmc1_aig_witness_out                  false
% 3.00/1.02  --bmc1_verbose                          false
% 3.00/1.02  --bmc1_dump_clauses_tptp                false
% 3.00/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.02  --bmc1_dump_file                        -
% 3.00/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.02  --bmc1_ucm_extend_mode                  1
% 3.00/1.02  --bmc1_ucm_init_mode                    2
% 3.00/1.02  --bmc1_ucm_cone_mode                    none
% 3.00/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.02  --bmc1_ucm_relax_model                  4
% 3.00/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.02  --bmc1_ucm_layered_model                none
% 3.00/1.02  --bmc1_ucm_max_lemma_size               10
% 3.00/1.02  
% 3.00/1.02  ------ AIG Options
% 3.00/1.02  
% 3.00/1.02  --aig_mode                              false
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation Options
% 3.00/1.02  
% 3.00/1.02  --instantiation_flag                    true
% 3.00/1.02  --inst_sos_flag                         false
% 3.00/1.02  --inst_sos_phase                        true
% 3.00/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.02  --inst_lit_sel_side                     none
% 3.00/1.02  --inst_solver_per_active                1400
% 3.00/1.02  --inst_solver_calls_frac                1.
% 3.00/1.02  --inst_passive_queue_type               priority_queues
% 3.00/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.02  --inst_passive_queues_freq              [25;2]
% 3.00/1.02  --inst_dismatching                      true
% 3.00/1.02  --inst_eager_unprocessed_to_passive     true
% 3.00/1.02  --inst_prop_sim_given                   true
% 3.00/1.02  --inst_prop_sim_new                     false
% 3.00/1.02  --inst_subs_new                         false
% 3.00/1.02  --inst_eq_res_simp                      false
% 3.00/1.02  --inst_subs_given                       false
% 3.00/1.02  --inst_orphan_elimination               true
% 3.00/1.02  --inst_learning_loop_flag               true
% 3.00/1.02  --inst_learning_start                   3000
% 3.00/1.02  --inst_learning_factor                  2
% 3.00/1.02  --inst_start_prop_sim_after_learn       3
% 3.00/1.02  --inst_sel_renew                        solver
% 3.00/1.02  --inst_lit_activity_flag                true
% 3.00/1.02  --inst_restr_to_given                   false
% 3.00/1.02  --inst_activity_threshold               500
% 3.00/1.02  --inst_out_proof                        true
% 3.00/1.02  
% 3.00/1.02  ------ Resolution Options
% 3.00/1.02  
% 3.00/1.02  --resolution_flag                       false
% 3.00/1.02  --res_lit_sel                           adaptive
% 3.00/1.02  --res_lit_sel_side                      none
% 3.00/1.02  --res_ordering                          kbo
% 3.00/1.02  --res_to_prop_solver                    active
% 3.00/1.02  --res_prop_simpl_new                    false
% 3.00/1.02  --res_prop_simpl_given                  true
% 3.00/1.02  --res_passive_queue_type                priority_queues
% 3.00/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.02  --res_passive_queues_freq               [15;5]
% 3.00/1.02  --res_forward_subs                      full
% 3.00/1.02  --res_backward_subs                     full
% 3.00/1.02  --res_forward_subs_resolution           true
% 3.00/1.02  --res_backward_subs_resolution          true
% 3.00/1.02  --res_orphan_elimination                true
% 3.00/1.02  --res_time_limit                        2.
% 3.00/1.02  --res_out_proof                         true
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Options
% 3.00/1.02  
% 3.00/1.02  --superposition_flag                    true
% 3.00/1.02  --sup_passive_queue_type                priority_queues
% 3.00/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.02  --demod_completeness_check              fast
% 3.00/1.02  --demod_use_ground                      true
% 3.00/1.02  --sup_to_prop_solver                    passive
% 3.00/1.02  --sup_prop_simpl_new                    true
% 3.00/1.02  --sup_prop_simpl_given                  true
% 3.00/1.02  --sup_fun_splitting                     false
% 3.00/1.02  --sup_smt_interval                      50000
% 3.00/1.02  
% 3.00/1.02  ------ Superposition Simplification Setup
% 3.00/1.02  
% 3.00/1.02  --sup_indices_passive                   []
% 3.00/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_full_bw                           [BwDemod]
% 3.00/1.02  --sup_immed_triv                        [TrivRules]
% 3.00/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_immed_bw_main                     []
% 3.00/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.02  
% 3.00/1.02  ------ Combination Options
% 3.00/1.02  
% 3.00/1.02  --comb_res_mult                         3
% 3.00/1.02  --comb_sup_mult                         2
% 3.00/1.02  --comb_inst_mult                        10
% 3.00/1.02  
% 3.00/1.02  ------ Debug Options
% 3.00/1.02  
% 3.00/1.02  --dbg_backtrace                         false
% 3.00/1.02  --dbg_dump_prop_clauses                 false
% 3.00/1.02  --dbg_dump_prop_clauses_file            -
% 3.00/1.02  --dbg_out_stat                          false
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  ------ Proving...
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  % SZS status Theorem for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02   Resolution empty clause
% 3.00/1.02  
% 3.00/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  fof(f8,axiom,(
% 3.00/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f18,plain,(
% 3.00/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 3.00/1.02    inference(ennf_transformation,[],[f8])).
% 3.00/1.02  
% 3.00/1.02  fof(f24,plain,(
% 3.00/1.02    ! [X6,X5,X4,X3,X2,X1,X0,X7] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 3.00/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.00/1.02  
% 3.00/1.02  fof(f25,plain,(
% 3.00/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> sP0(X6,X5,X4,X3,X2,X1,X0,X7))),
% 3.00/1.02    inference(definition_folding,[],[f18,f24])).
% 3.00/1.02  
% 3.00/1.02  fof(f31,plain,(
% 3.00/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)) & (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 3.00/1.02    inference(nnf_transformation,[],[f25])).
% 3.00/1.02  
% 3.00/1.02  fof(f59,plain,(
% 3.00/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 3.00/1.02    inference(cnf_transformation,[],[f31])).
% 3.00/1.02  
% 3.00/1.02  fof(f5,axiom,(
% 3.00/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f40,plain,(
% 3.00/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f5])).
% 3.00/1.02  
% 3.00/1.02  fof(f76,plain,(
% 3.00/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 3.00/1.02    inference(definition_unfolding,[],[f59,f40])).
% 3.00/1.02  
% 3.00/1.02  fof(f85,plain,(
% 3.00/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 3.00/1.02    inference(equality_resolution,[],[f76])).
% 3.00/1.02  
% 3.00/1.02  fof(f26,plain,(
% 3.00/1.02    ! [X6,X5,X4,X3,X2,X1,X0,X7] : ((sP0(X6,X5,X4,X3,X2,X1,X0,X7) | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | ~r2_hidden(X8,X7))) | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)))),
% 3.00/1.02    inference(nnf_transformation,[],[f24])).
% 3.00/1.02  
% 3.00/1.02  fof(f27,plain,(
% 3.00/1.02    ! [X6,X5,X4,X3,X2,X1,X0,X7] : ((sP0(X6,X5,X4,X3,X2,X1,X0,X7) | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X7))) | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)))),
% 3.00/1.02    inference(flattening,[],[f26])).
% 3.00/1.02  
% 3.00/1.02  fof(f28,plain,(
% 3.00/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : (((X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8 & X6 != X8) | ~r2_hidden(X8,X7)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | X6 = X8 | r2_hidden(X8,X7)))) & (! [X9] : ((r2_hidden(X9,X7) | (X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | ~r2_hidden(X9,X7))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 3.00/1.02    inference(rectify,[],[f27])).
% 3.00/1.02  
% 3.00/1.02  fof(f29,plain,(
% 3.00/1.02    ! [X7,X6,X5,X4,X3,X2,X1,X0] : (? [X8] : (((X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8 & X6 != X8) | ~r2_hidden(X8,X7)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | X6 = X8 | r2_hidden(X8,X7))) => (((sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7))))),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f30,plain,(
% 3.00/1.02    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | (((sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)))) & (! [X9] : ((r2_hidden(X9,X7) | (X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | ~r2_hidden(X9,X7))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 3.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 3.00/1.02  
% 3.00/1.02  fof(f50,plain,(
% 3.00/1.02    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | X0 != X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f30])).
% 3.00/1.02  
% 3.00/1.02  fof(f78,plain,(
% 3.00/1.02    ( ! [X6,X4,X2,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | ~sP0(X9,X1,X2,X3,X4,X5,X6,X7)) )),
% 3.00/1.02    inference(equality_resolution,[],[f50])).
% 3.00/1.02  
% 3.00/1.02  fof(f14,conjecture,(
% 3.00/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f15,negated_conjecture,(
% 3.00/1.02    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 3.00/1.02    inference(negated_conjecture,[],[f14])).
% 3.00/1.02  
% 3.00/1.02  fof(f23,plain,(
% 3.00/1.02    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f15])).
% 3.00/1.02  
% 3.00/1.02  fof(f34,plain,(
% 3.00/1.02    ( ! [X0,X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,sK4)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f33,plain,(
% 3.00/1.02    ( ! [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),sK3,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f32,plain,(
% 3.00/1.02    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 3.00/1.02    introduced(choice_axiom,[])).
% 3.00/1.02  
% 3.00/1.02  fof(f35,plain,(
% 3.00/1.02    ((~m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 3.00/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f34,f33,f32])).
% 3.00/1.02  
% 3.00/1.02  fof(f68,plain,(
% 3.00/1.02    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.00/1.02    inference(cnf_transformation,[],[f35])).
% 3.00/1.02  
% 3.00/1.02  fof(f9,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f19,plain,(
% 3.00/1.02    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.00/1.02    inference(ennf_transformation,[],[f9])).
% 3.00/1.02  
% 3.00/1.02  fof(f61,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f19])).
% 3.00/1.02  
% 3.00/1.02  fof(f10,axiom,(
% 3.00/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f62,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.00/1.02    inference(cnf_transformation,[],[f10])).
% 3.00/1.02  
% 3.00/1.02  fof(f1,axiom,(
% 3.00/1.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f36,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f1])).
% 3.00/1.02  
% 3.00/1.02  fof(f2,axiom,(
% 3.00/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f37,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f2])).
% 3.00/1.02  
% 3.00/1.02  fof(f3,axiom,(
% 3.00/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f38,plain,(
% 3.00/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f3])).
% 3.00/1.02  
% 3.00/1.02  fof(f4,axiom,(
% 3.00/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f39,plain,(
% 3.00/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f4])).
% 3.00/1.02  
% 3.00/1.02  fof(f6,axiom,(
% 3.00/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f41,plain,(
% 3.00/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f6])).
% 3.00/1.02  
% 3.00/1.02  fof(f70,plain,(
% 3.00/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.00/1.02    inference(definition_unfolding,[],[f39,f41])).
% 3.00/1.02  
% 3.00/1.02  fof(f71,plain,(
% 3.00/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.00/1.02    inference(definition_unfolding,[],[f38,f70])).
% 3.00/1.02  
% 3.00/1.02  fof(f72,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.00/1.02    inference(definition_unfolding,[],[f37,f71])).
% 3.00/1.02  
% 3.00/1.02  fof(f73,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.00/1.02    inference(definition_unfolding,[],[f36,f72])).
% 3.00/1.02  
% 3.00/1.02  fof(f74,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.00/1.02    inference(definition_unfolding,[],[f62,f73])).
% 3.00/1.02  
% 3.00/1.02  fof(f77,plain,(
% 3.00/1.02    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.00/1.02    inference(definition_unfolding,[],[f61,f74])).
% 3.00/1.02  
% 3.00/1.02  fof(f11,axiom,(
% 3.00/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f16,plain,(
% 3.00/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.00/1.02    inference(unused_predicate_definition_removal,[],[f11])).
% 3.00/1.02  
% 3.00/1.02  fof(f20,plain,(
% 3.00/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.00/1.02    inference(ennf_transformation,[],[f16])).
% 3.00/1.02  
% 3.00/1.02  fof(f63,plain,(
% 3.00/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f20])).
% 3.00/1.02  
% 3.00/1.02  fof(f12,axiom,(
% 3.00/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f21,plain,(
% 3.00/1.02    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 3.00/1.02    inference(ennf_transformation,[],[f12])).
% 3.00/1.02  
% 3.00/1.02  fof(f64,plain,(
% 3.00/1.02    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f21])).
% 3.00/1.02  
% 3.00/1.02  fof(f13,axiom,(
% 3.00/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 3.00/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.02  
% 3.00/1.02  fof(f22,plain,(
% 3.00/1.02    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.00/1.02    inference(ennf_transformation,[],[f13])).
% 3.00/1.02  
% 3.00/1.02  fof(f65,plain,(
% 3.00/1.02    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f22])).
% 3.00/1.02  
% 3.00/1.02  fof(f66,plain,(
% 3.00/1.02    l1_pre_topc(sK2)),
% 3.00/1.02    inference(cnf_transformation,[],[f35])).
% 3.00/1.02  
% 3.00/1.02  fof(f69,plain,(
% 3.00/1.02    ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4))))),
% 3.00/1.02    inference(cnf_transformation,[],[f35])).
% 3.00/1.02  
% 3.00/1.02  cnf(c_18,plain,
% 3.00/1.02      ( sP0(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6937,plain,
% 3.00/1.02      ( sP0(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0)) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_9,plain,
% 3.00/1.02      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) | r2_hidden(X0,X7) ),
% 3.00/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6946,plain,
% 3.00/1.02      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7) != iProver_top
% 3.00/1.02      | r2_hidden(X0,X7) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_9278,plain,
% 3.00/1.02      ( r2_hidden(X0,k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X0)) = iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_6937,c_6946]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_24,negated_conjecture,
% 3.00/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6934,plain,
% 3.00/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_19,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.00/1.02      | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6936,plain,
% 3.00/1.02      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.00/1.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_7394,plain,
% 3.00/1.02      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK4)) = k9_subset_1(u1_struct_0(sK2),X0,sK4) ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_6934,c_6936]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_20,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_21,plain,
% 3.00/1.02      ( r1_tarski(k1_setfam_1(X0),X1) | ~ r2_hidden(X1,X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_290,plain,
% 3.00/1.02      ( ~ r2_hidden(X0,X1)
% 3.00/1.02      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.00/1.02      | X0 != X3
% 3.00/1.02      | k1_setfam_1(X1) != X2 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_21]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_291,plain,
% 3.00/1.02      ( ~ r2_hidden(X0,X1) | m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X0)) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_290]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6932,plain,
% 3.00/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.00/1.02      | m1_subset_1(k1_setfam_1(X1),k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_7719,plain,
% 3.00/1.02      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,sK4)) != iProver_top
% 3.00/1.02      | m1_subset_1(k9_subset_1(u1_struct_0(sK2),X1,sK4),k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_7394,c_6932]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_9589,plain,
% 3.00/1.02      ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,sK4),k1_zfmisc_1(sK4)) = iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_9278,c_7719]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_22,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.02      | ~ l1_pre_topc(X1)
% 3.00/1.02      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_26,negated_conjecture,
% 3.00/1.02      ( l1_pre_topc(sK2) ),
% 3.00/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_305,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.00/1.02      | u1_struct_0(k1_pre_topc(X1,X0)) = X0
% 3.00/1.02      | sK2 != X1 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_306,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.00/1.02      | u1_struct_0(k1_pre_topc(sK2,X0)) = X0 ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_305]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6931,plain,
% 3.00/1.02      ( u1_struct_0(k1_pre_topc(sK2,X0)) = X0
% 3.00/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_7178,plain,
% 3.00/1.03      ( u1_struct_0(k1_pre_topc(sK2,sK4)) = sK4 ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_6934,c_6931]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_23,negated_conjecture,
% 3.00/1.03      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) ),
% 3.00/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_6935,plain,
% 3.00/1.03      ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK2,sK4)))) != iProver_top ),
% 3.00/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_7211,plain,
% 3.00/1.03      ( m1_subset_1(k9_subset_1(u1_struct_0(sK2),sK3,sK4),k1_zfmisc_1(sK4)) != iProver_top ),
% 3.00/1.03      inference(demodulation,[status(thm)],[c_7178,c_6935]) ).
% 3.00/1.03  
% 3.00/1.03  cnf(c_9612,plain,
% 3.00/1.03      ( $false ),
% 3.00/1.03      inference(superposition,[status(thm)],[c_9589,c_7211]) ).
% 3.00/1.03  
% 3.00/1.03  
% 3.00/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.03  
% 3.00/1.03  ------                               Statistics
% 3.00/1.03  
% 3.00/1.03  ------ General
% 3.00/1.03  
% 3.00/1.03  abstr_ref_over_cycles:                  0
% 3.00/1.03  abstr_ref_under_cycles:                 0
% 3.00/1.03  gc_basic_clause_elim:                   0
% 3.00/1.03  forced_gc_time:                         0
% 3.00/1.03  parsing_time:                           0.012
% 3.00/1.03  unif_index_cands_time:                  0.
% 3.00/1.03  unif_index_add_time:                    0.
% 3.00/1.03  orderings_time:                         0.
% 3.00/1.03  out_proof_time:                         0.008
% 3.00/1.03  total_time:                             0.289
% 3.00/1.03  num_of_symbols:                         46
% 3.00/1.03  num_of_terms:                           6249
% 3.00/1.03  
% 3.00/1.03  ------ Preprocessing
% 3.00/1.03  
% 3.00/1.03  num_of_splits:                          0
% 3.00/1.03  num_of_split_atoms:                     0
% 3.00/1.03  num_of_reused_defs:                     0
% 3.00/1.03  num_eq_ax_congr_red:                    73
% 3.00/1.03  num_of_sem_filtered_clauses:            1
% 3.00/1.03  num_of_subtypes:                        0
% 3.00/1.03  monotx_restored_types:                  0
% 3.00/1.03  sat_num_of_epr_types:                   0
% 3.00/1.03  sat_num_of_non_cyclic_types:            0
% 3.00/1.03  sat_guarded_non_collapsed_types:        0
% 3.00/1.03  num_pure_diseq_elim:                    0
% 3.00/1.03  simp_replaced_by:                       0
% 3.00/1.03  res_preprocessed:                       123
% 3.00/1.03  prep_upred:                             0
% 3.00/1.03  prep_unflattend:                        425
% 3.00/1.03  smt_new_axioms:                         0
% 3.00/1.03  pred_elim_cands:                        3
% 3.00/1.03  pred_elim:                              2
% 3.00/1.03  pred_elim_cl:                           2
% 3.00/1.03  pred_elim_cycles:                       8
% 3.00/1.03  merged_defs:                            0
% 3.00/1.03  merged_defs_ncl:                        0
% 3.00/1.03  bin_hyper_res:                          0
% 3.00/1.03  prep_cycles:                            4
% 3.00/1.03  pred_elim_time:                         0.107
% 3.00/1.03  splitting_time:                         0.
% 3.00/1.03  sem_filter_time:                        0.
% 3.00/1.03  monotx_time:                            0.001
% 3.00/1.03  subtype_inf_time:                       0.
% 3.00/1.03  
% 3.00/1.03  ------ Problem properties
% 3.00/1.03  
% 3.00/1.03  clauses:                                25
% 3.00/1.03  conjectures:                            3
% 3.00/1.03  epr:                                    8
% 3.00/1.03  horn:                                   23
% 3.00/1.03  ground:                                 3
% 3.00/1.03  unary:                                  4
% 3.00/1.03  binary:                                 12
% 3.00/1.03  lits:                                   67
% 3.00/1.03  lits_eq:                                25
% 3.00/1.03  fd_pure:                                0
% 3.00/1.03  fd_pseudo:                              0
% 3.00/1.03  fd_cond:                                0
% 3.00/1.03  fd_pseudo_cond:                         2
% 3.00/1.03  ac_symbols:                             0
% 3.00/1.03  
% 3.00/1.03  ------ Propositional Solver
% 3.00/1.03  
% 3.00/1.03  prop_solver_calls:                      26
% 3.00/1.03  prop_fast_solver_calls:                 1933
% 3.00/1.03  smt_solver_calls:                       0
% 3.00/1.03  smt_fast_solver_calls:                  0
% 3.00/1.03  prop_num_of_clauses:                    1734
% 3.00/1.03  prop_preprocess_simplified:             8512
% 3.00/1.03  prop_fo_subsumed:                       0
% 3.00/1.03  prop_solver_time:                       0.
% 3.00/1.03  smt_solver_time:                        0.
% 3.00/1.03  smt_fast_solver_time:                   0.
% 3.00/1.03  prop_fast_solver_time:                  0.
% 3.00/1.03  prop_unsat_core_time:                   0.
% 3.00/1.03  
% 3.00/1.03  ------ QBF
% 3.00/1.03  
% 3.00/1.03  qbf_q_res:                              0
% 3.00/1.03  qbf_num_tautologies:                    0
% 3.00/1.03  qbf_prep_cycles:                        0
% 3.00/1.03  
% 3.00/1.03  ------ BMC1
% 3.00/1.03  
% 3.00/1.03  bmc1_current_bound:                     -1
% 3.00/1.03  bmc1_last_solved_bound:                 -1
% 3.00/1.03  bmc1_unsat_core_size:                   -1
% 3.00/1.03  bmc1_unsat_core_parents_size:           -1
% 3.00/1.03  bmc1_merge_next_fun:                    0
% 3.00/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.03  
% 3.00/1.03  ------ Instantiation
% 3.00/1.03  
% 3.00/1.03  inst_num_of_clauses:                    475
% 3.00/1.03  inst_num_in_passive:                    166
% 3.00/1.03  inst_num_in_active:                     136
% 3.00/1.03  inst_num_in_unprocessed:                173
% 3.00/1.03  inst_num_of_loops:                      140
% 3.00/1.03  inst_num_of_learning_restarts:          0
% 3.00/1.03  inst_num_moves_active_passive:          2
% 3.00/1.03  inst_lit_activity:                      0
% 3.00/1.03  inst_lit_activity_moves:                0
% 3.00/1.03  inst_num_tautologies:                   0
% 3.00/1.03  inst_num_prop_implied:                  0
% 3.00/1.03  inst_num_existing_simplified:           0
% 3.00/1.03  inst_num_eq_res_simplified:             0
% 3.00/1.03  inst_num_child_elim:                    0
% 3.00/1.03  inst_num_of_dismatching_blockings:      65
% 3.00/1.03  inst_num_of_non_proper_insts:           361
% 3.00/1.03  inst_num_of_duplicates:                 0
% 3.00/1.03  inst_inst_num_from_inst_to_res:         0
% 3.00/1.03  inst_dismatching_checking_time:         0.
% 3.00/1.03  
% 3.00/1.03  ------ Resolution
% 3.00/1.03  
% 3.00/1.03  res_num_of_clauses:                     0
% 3.00/1.03  res_num_in_passive:                     0
% 3.00/1.03  res_num_in_active:                      0
% 3.00/1.03  res_num_of_loops:                       127
% 3.00/1.03  res_forward_subset_subsumed:            98
% 3.00/1.03  res_backward_subset_subsumed:           0
% 3.00/1.03  res_forward_subsumed:                   0
% 3.00/1.03  res_backward_subsumed:                  0
% 3.00/1.03  res_forward_subsumption_resolution:     0
% 3.00/1.03  res_backward_subsumption_resolution:    0
% 3.00/1.03  res_clause_to_clause_subsumption:       5371
% 3.00/1.03  res_orphan_elimination:                 0
% 3.00/1.03  res_tautology_del:                      23
% 3.00/1.03  res_num_eq_res_simplified:              0
% 3.00/1.03  res_num_sel_changes:                    0
% 3.00/1.03  res_moves_from_active_to_pass:          0
% 3.00/1.03  
% 3.00/1.03  ------ Superposition
% 3.00/1.03  
% 3.00/1.03  sup_time_total:                         0.
% 3.00/1.03  sup_time_generating:                    0.
% 3.00/1.03  sup_time_sim_full:                      0.
% 3.00/1.03  sup_time_sim_immed:                     0.
% 3.00/1.03  
% 3.00/1.03  sup_num_of_clauses:                     47
% 3.00/1.03  sup_num_in_active:                      27
% 3.00/1.03  sup_num_in_passive:                     20
% 3.00/1.03  sup_num_of_loops:                       27
% 3.00/1.03  sup_fw_superposition:                   9
% 3.00/1.03  sup_bw_superposition:                   16
% 3.00/1.03  sup_immediate_simplified:               0
% 3.00/1.03  sup_given_eliminated:                   0
% 3.00/1.03  comparisons_done:                       0
% 3.00/1.03  comparisons_avoided:                    0
% 3.00/1.03  
% 3.00/1.03  ------ Simplifications
% 3.00/1.03  
% 3.00/1.03  
% 3.00/1.03  sim_fw_subset_subsumed:                 0
% 3.00/1.03  sim_bw_subset_subsumed:                 0
% 3.00/1.03  sim_fw_subsumed:                        0
% 3.00/1.03  sim_bw_subsumed:                        0
% 3.00/1.03  sim_fw_subsumption_res:                 0
% 3.00/1.03  sim_bw_subsumption_res:                 0
% 3.00/1.03  sim_tautology_del:                      0
% 3.00/1.03  sim_eq_tautology_del:                   0
% 3.00/1.03  sim_eq_res_simp:                        0
% 3.00/1.03  sim_fw_demodulated:                     0
% 3.00/1.03  sim_bw_demodulated:                     1
% 3.00/1.03  sim_light_normalised:                   0
% 3.00/1.03  sim_joinable_taut:                      0
% 3.00/1.03  sim_joinable_simp:                      0
% 3.00/1.03  sim_ac_normalised:                      0
% 3.00/1.03  sim_smt_subsumption:                    0
% 3.00/1.03  
%------------------------------------------------------------------------------
