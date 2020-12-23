%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:46 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 382 expanded)
%              Number of clauses        :   48 ( 105 expanded)
%              Number of leaves         :   15 ( 125 expanded)
%              Depth                    :   17
%              Number of atoms          :  296 (1971 expanded)
%              Number of equality atoms :   88 ( 392 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f29,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v4_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v4_pre_topc(sK4,X2)
        & sK4 = X1
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(X3,X2)
              & X1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v4_pre_topc(X1,X0)
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ~ v4_pre_topc(X3,sK3)
            & X1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
        & v4_pre_topc(X1,X0)
        & m1_pre_topc(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(X3,X2)
                & sK2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v4_pre_topc(sK2,X0)
            & m1_pre_topc(X2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v4_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,sK1)
              & m1_pre_topc(X2,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ v4_pre_topc(sK4,sK3)
    & sK2 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v4_pre_topc(sK2,sK1)
    & m1_pre_topc(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f29,f28,f27,f26])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ~ v4_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_636,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_205,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_6,c_5])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_219,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_220,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_222,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_220,c_18])).

cnf(c_341,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_205,c_222])).

cnf(c_342,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_656,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_636,c_342])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_4,c_0])).

cnf(c_633,plain,
    ( k3_xboole_0(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_1002,plain,
    ( k3_xboole_0(sK4,k2_struct_0(sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_656,c_633])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_639,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_659,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_639,c_1])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_638,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1129,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_659,c_638])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_230,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_231,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_235,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
    | ~ v4_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_231,c_18])).

cnf(c_236,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_235])).

cnf(c_632,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_336,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_205,c_18])).

cnf(c_337,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_691,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_632,c_337,c_342])).

cnf(c_1599,plain,
    ( v4_pre_topc(X0,sK1) != iProver_top
    | v4_pre_topc(k3_xboole_0(X0,k2_struct_0(sK3)),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_xboole_0(X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1129,c_691])).

cnf(c_1753,plain,
    ( v4_pre_topc(k3_xboole_0(sK4,k2_struct_0(sK3)),sK3) = iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1002,c_1599])).

cnf(c_1768,plain,
    ( v4_pre_topc(sK4,sK1) != iProver_top
    | v4_pre_topc(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1753,c_1002])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_634,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,negated_conjecture,
    ( sK2 = sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_653,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_634,c_13,c_337])).

cnf(c_15,negated_conjecture,
    ( v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_635,plain,
    ( v4_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_648,plain,
    ( v4_pre_topc(sK4,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_635,c_13])).

cnf(c_12,negated_conjecture,
    ( ~ v4_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( v4_pre_topc(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1768,c_653,c_648,c_656,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.52/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.03  
% 2.52/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/1.03  
% 2.52/1.03  ------  iProver source info
% 2.52/1.03  
% 2.52/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.52/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/1.03  git: non_committed_changes: false
% 2.52/1.03  git: last_make_outside_of_git: false
% 2.52/1.03  
% 2.52/1.03  ------ 
% 2.52/1.03  
% 2.52/1.03  ------ Input Options
% 2.52/1.03  
% 2.52/1.03  --out_options                           all
% 2.52/1.03  --tptp_safe_out                         true
% 2.52/1.03  --problem_path                          ""
% 2.52/1.03  --include_path                          ""
% 2.52/1.03  --clausifier                            res/vclausify_rel
% 2.52/1.03  --clausifier_options                    --mode clausify
% 2.52/1.03  --stdin                                 false
% 2.52/1.03  --stats_out                             all
% 2.52/1.03  
% 2.52/1.03  ------ General Options
% 2.52/1.03  
% 2.52/1.03  --fof                                   false
% 2.52/1.03  --time_out_real                         305.
% 2.52/1.03  --time_out_virtual                      -1.
% 2.52/1.03  --symbol_type_check                     false
% 2.52/1.03  --clausify_out                          false
% 2.52/1.03  --sig_cnt_out                           false
% 2.52/1.03  --trig_cnt_out                          false
% 2.52/1.03  --trig_cnt_out_tolerance                1.
% 2.52/1.03  --trig_cnt_out_sk_spl                   false
% 2.52/1.03  --abstr_cl_out                          false
% 2.52/1.03  
% 2.52/1.03  ------ Global Options
% 2.52/1.03  
% 2.52/1.03  --schedule                              default
% 2.52/1.03  --add_important_lit                     false
% 2.52/1.03  --prop_solver_per_cl                    1000
% 2.52/1.03  --min_unsat_core                        false
% 2.52/1.03  --soft_assumptions                      false
% 2.52/1.03  --soft_lemma_size                       3
% 2.52/1.03  --prop_impl_unit_size                   0
% 2.52/1.03  --prop_impl_unit                        []
% 2.52/1.03  --share_sel_clauses                     true
% 2.52/1.03  --reset_solvers                         false
% 2.52/1.03  --bc_imp_inh                            [conj_cone]
% 2.52/1.03  --conj_cone_tolerance                   3.
% 2.52/1.03  --extra_neg_conj                        none
% 2.52/1.03  --large_theory_mode                     true
% 2.52/1.03  --prolific_symb_bound                   200
% 2.52/1.03  --lt_threshold                          2000
% 2.52/1.03  --clause_weak_htbl                      true
% 2.52/1.03  --gc_record_bc_elim                     false
% 2.52/1.03  
% 2.52/1.03  ------ Preprocessing Options
% 2.52/1.03  
% 2.52/1.03  --preprocessing_flag                    true
% 2.52/1.03  --time_out_prep_mult                    0.1
% 2.52/1.03  --splitting_mode                        input
% 2.52/1.03  --splitting_grd                         true
% 2.52/1.03  --splitting_cvd                         false
% 2.52/1.03  --splitting_cvd_svl                     false
% 2.52/1.03  --splitting_nvd                         32
% 2.52/1.03  --sub_typing                            true
% 2.52/1.03  --prep_gs_sim                           true
% 2.52/1.03  --prep_unflatten                        true
% 2.52/1.03  --prep_res_sim                          true
% 2.52/1.03  --prep_upred                            true
% 2.52/1.03  --prep_sem_filter                       exhaustive
% 2.52/1.03  --prep_sem_filter_out                   false
% 2.52/1.03  --pred_elim                             true
% 2.52/1.03  --res_sim_input                         true
% 2.52/1.03  --eq_ax_congr_red                       true
% 2.52/1.03  --pure_diseq_elim                       true
% 2.52/1.03  --brand_transform                       false
% 2.52/1.03  --non_eq_to_eq                          false
% 2.52/1.03  --prep_def_merge                        true
% 2.52/1.03  --prep_def_merge_prop_impl              false
% 2.52/1.03  --prep_def_merge_mbd                    true
% 2.52/1.03  --prep_def_merge_tr_red                 false
% 2.52/1.03  --prep_def_merge_tr_cl                  false
% 2.52/1.03  --smt_preprocessing                     true
% 2.52/1.03  --smt_ac_axioms                         fast
% 2.52/1.03  --preprocessed_out                      false
% 2.52/1.03  --preprocessed_stats                    false
% 2.52/1.03  
% 2.52/1.03  ------ Abstraction refinement Options
% 2.52/1.03  
% 2.52/1.03  --abstr_ref                             []
% 2.52/1.03  --abstr_ref_prep                        false
% 2.52/1.03  --abstr_ref_until_sat                   false
% 2.52/1.03  --abstr_ref_sig_restrict                funpre
% 2.52/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/1.03  --abstr_ref_under                       []
% 2.52/1.03  
% 2.52/1.03  ------ SAT Options
% 2.52/1.03  
% 2.52/1.03  --sat_mode                              false
% 2.52/1.03  --sat_fm_restart_options                ""
% 2.52/1.03  --sat_gr_def                            false
% 2.52/1.03  --sat_epr_types                         true
% 2.52/1.03  --sat_non_cyclic_types                  false
% 2.52/1.03  --sat_finite_models                     false
% 2.52/1.03  --sat_fm_lemmas                         false
% 2.52/1.03  --sat_fm_prep                           false
% 2.52/1.03  --sat_fm_uc_incr                        true
% 2.52/1.03  --sat_out_model                         small
% 2.52/1.03  --sat_out_clauses                       false
% 2.52/1.03  
% 2.52/1.03  ------ QBF Options
% 2.52/1.03  
% 2.52/1.03  --qbf_mode                              false
% 2.52/1.03  --qbf_elim_univ                         false
% 2.52/1.03  --qbf_dom_inst                          none
% 2.52/1.03  --qbf_dom_pre_inst                      false
% 2.52/1.03  --qbf_sk_in                             false
% 2.52/1.03  --qbf_pred_elim                         true
% 2.52/1.03  --qbf_split                             512
% 2.52/1.03  
% 2.52/1.03  ------ BMC1 Options
% 2.52/1.03  
% 2.52/1.03  --bmc1_incremental                      false
% 2.52/1.03  --bmc1_axioms                           reachable_all
% 2.52/1.03  --bmc1_min_bound                        0
% 2.52/1.03  --bmc1_max_bound                        -1
% 2.52/1.03  --bmc1_max_bound_default                -1
% 2.52/1.03  --bmc1_symbol_reachability              true
% 2.52/1.03  --bmc1_property_lemmas                  false
% 2.52/1.03  --bmc1_k_induction                      false
% 2.52/1.03  --bmc1_non_equiv_states                 false
% 2.52/1.03  --bmc1_deadlock                         false
% 2.52/1.03  --bmc1_ucm                              false
% 2.52/1.03  --bmc1_add_unsat_core                   none
% 2.52/1.03  --bmc1_unsat_core_children              false
% 2.52/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/1.03  --bmc1_out_stat                         full
% 2.52/1.03  --bmc1_ground_init                      false
% 2.52/1.03  --bmc1_pre_inst_next_state              false
% 2.52/1.03  --bmc1_pre_inst_state                   false
% 2.52/1.03  --bmc1_pre_inst_reach_state             false
% 2.52/1.03  --bmc1_out_unsat_core                   false
% 2.52/1.03  --bmc1_aig_witness_out                  false
% 2.52/1.03  --bmc1_verbose                          false
% 2.52/1.03  --bmc1_dump_clauses_tptp                false
% 2.52/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.52/1.03  --bmc1_dump_file                        -
% 2.52/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.52/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.52/1.03  --bmc1_ucm_extend_mode                  1
% 2.52/1.03  --bmc1_ucm_init_mode                    2
% 2.52/1.03  --bmc1_ucm_cone_mode                    none
% 2.52/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.52/1.03  --bmc1_ucm_relax_model                  4
% 2.52/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.52/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/1.03  --bmc1_ucm_layered_model                none
% 2.52/1.03  --bmc1_ucm_max_lemma_size               10
% 2.52/1.03  
% 2.52/1.03  ------ AIG Options
% 2.52/1.03  
% 2.52/1.03  --aig_mode                              false
% 2.52/1.03  
% 2.52/1.03  ------ Instantiation Options
% 2.52/1.03  
% 2.52/1.03  --instantiation_flag                    true
% 2.52/1.03  --inst_sos_flag                         false
% 2.52/1.03  --inst_sos_phase                        true
% 2.52/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/1.03  --inst_lit_sel_side                     num_symb
% 2.52/1.03  --inst_solver_per_active                1400
% 2.52/1.03  --inst_solver_calls_frac                1.
% 2.52/1.03  --inst_passive_queue_type               priority_queues
% 2.52/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/1.03  --inst_passive_queues_freq              [25;2]
% 2.52/1.03  --inst_dismatching                      true
% 2.52/1.03  --inst_eager_unprocessed_to_passive     true
% 2.52/1.03  --inst_prop_sim_given                   true
% 2.52/1.03  --inst_prop_sim_new                     false
% 2.52/1.03  --inst_subs_new                         false
% 2.52/1.03  --inst_eq_res_simp                      false
% 2.52/1.03  --inst_subs_given                       false
% 2.52/1.03  --inst_orphan_elimination               true
% 2.52/1.03  --inst_learning_loop_flag               true
% 2.52/1.03  --inst_learning_start                   3000
% 2.52/1.03  --inst_learning_factor                  2
% 2.52/1.03  --inst_start_prop_sim_after_learn       3
% 2.52/1.03  --inst_sel_renew                        solver
% 2.52/1.03  --inst_lit_activity_flag                true
% 2.52/1.03  --inst_restr_to_given                   false
% 2.52/1.03  --inst_activity_threshold               500
% 2.52/1.03  --inst_out_proof                        true
% 2.52/1.03  
% 2.52/1.03  ------ Resolution Options
% 2.52/1.03  
% 2.52/1.03  --resolution_flag                       true
% 2.52/1.03  --res_lit_sel                           adaptive
% 2.52/1.03  --res_lit_sel_side                      none
% 2.52/1.03  --res_ordering                          kbo
% 2.52/1.03  --res_to_prop_solver                    active
% 2.52/1.03  --res_prop_simpl_new                    false
% 2.52/1.03  --res_prop_simpl_given                  true
% 2.52/1.03  --res_passive_queue_type                priority_queues
% 2.52/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/1.03  --res_passive_queues_freq               [15;5]
% 2.52/1.03  --res_forward_subs                      full
% 2.52/1.03  --res_backward_subs                     full
% 2.52/1.03  --res_forward_subs_resolution           true
% 2.52/1.03  --res_backward_subs_resolution          true
% 2.52/1.03  --res_orphan_elimination                true
% 2.52/1.03  --res_time_limit                        2.
% 2.52/1.03  --res_out_proof                         true
% 2.52/1.03  
% 2.52/1.03  ------ Superposition Options
% 2.52/1.03  
% 2.52/1.03  --superposition_flag                    true
% 2.52/1.03  --sup_passive_queue_type                priority_queues
% 2.52/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.52/1.03  --demod_completeness_check              fast
% 2.52/1.03  --demod_use_ground                      true
% 2.52/1.03  --sup_to_prop_solver                    passive
% 2.52/1.03  --sup_prop_simpl_new                    true
% 2.52/1.03  --sup_prop_simpl_given                  true
% 2.52/1.03  --sup_fun_splitting                     false
% 2.52/1.03  --sup_smt_interval                      50000
% 2.52/1.03  
% 2.52/1.03  ------ Superposition Simplification Setup
% 2.52/1.03  
% 2.52/1.03  --sup_indices_passive                   []
% 2.52/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.03  --sup_full_bw                           [BwDemod]
% 2.52/1.03  --sup_immed_triv                        [TrivRules]
% 2.52/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.03  --sup_immed_bw_main                     []
% 2.52/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.03  
% 2.52/1.03  ------ Combination Options
% 2.52/1.03  
% 2.52/1.03  --comb_res_mult                         3
% 2.52/1.03  --comb_sup_mult                         2
% 2.52/1.03  --comb_inst_mult                        10
% 2.52/1.03  
% 2.52/1.03  ------ Debug Options
% 2.52/1.03  
% 2.52/1.03  --dbg_backtrace                         false
% 2.52/1.03  --dbg_dump_prop_clauses                 false
% 2.52/1.03  --dbg_dump_prop_clauses_file            -
% 2.52/1.03  --dbg_out_stat                          false
% 2.52/1.03  ------ Parsing...
% 2.52/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/1.03  
% 2.52/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.52/1.03  
% 2.52/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/1.03  
% 2.52/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/1.03  ------ Proving...
% 2.52/1.03  ------ Problem Properties 
% 2.52/1.03  
% 2.52/1.03  
% 2.52/1.03  clauses                                 15
% 2.52/1.03  conjectures                             5
% 2.52/1.03  EPR                                     3
% 2.52/1.03  Horn                                    15
% 2.52/1.03  unary                                   9
% 2.52/1.03  binary                                  2
% 2.52/1.03  lits                                    26
% 2.52/1.03  lits eq                                 7
% 2.52/1.03  fd_pure                                 0
% 2.52/1.03  fd_pseudo                               0
% 2.52/1.03  fd_cond                                 0
% 2.52/1.03  fd_pseudo_cond                          0
% 2.52/1.03  AC symbols                              0
% 2.52/1.03  
% 2.52/1.03  ------ Schedule dynamic 5 is on 
% 2.52/1.03  
% 2.52/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/1.03  
% 2.52/1.03  
% 2.52/1.03  ------ 
% 2.52/1.03  Current options:
% 2.52/1.03  ------ 
% 2.52/1.03  
% 2.52/1.03  ------ Input Options
% 2.52/1.03  
% 2.52/1.03  --out_options                           all
% 2.52/1.03  --tptp_safe_out                         true
% 2.52/1.03  --problem_path                          ""
% 2.52/1.03  --include_path                          ""
% 2.52/1.03  --clausifier                            res/vclausify_rel
% 2.52/1.03  --clausifier_options                    --mode clausify
% 2.52/1.03  --stdin                                 false
% 2.52/1.03  --stats_out                             all
% 2.52/1.03  
% 2.52/1.03  ------ General Options
% 2.52/1.03  
% 2.52/1.03  --fof                                   false
% 2.52/1.03  --time_out_real                         305.
% 2.52/1.03  --time_out_virtual                      -1.
% 2.52/1.03  --symbol_type_check                     false
% 2.52/1.03  --clausify_out                          false
% 2.52/1.03  --sig_cnt_out                           false
% 2.52/1.03  --trig_cnt_out                          false
% 2.52/1.03  --trig_cnt_out_tolerance                1.
% 2.52/1.03  --trig_cnt_out_sk_spl                   false
% 2.52/1.03  --abstr_cl_out                          false
% 2.52/1.03  
% 2.52/1.03  ------ Global Options
% 2.52/1.03  
% 2.52/1.03  --schedule                              default
% 2.52/1.03  --add_important_lit                     false
% 2.52/1.03  --prop_solver_per_cl                    1000
% 2.52/1.03  --min_unsat_core                        false
% 2.52/1.03  --soft_assumptions                      false
% 2.52/1.03  --soft_lemma_size                       3
% 2.52/1.03  --prop_impl_unit_size                   0
% 2.52/1.03  --prop_impl_unit                        []
% 2.52/1.03  --share_sel_clauses                     true
% 2.52/1.03  --reset_solvers                         false
% 2.52/1.03  --bc_imp_inh                            [conj_cone]
% 2.52/1.03  --conj_cone_tolerance                   3.
% 2.52/1.03  --extra_neg_conj                        none
% 2.52/1.03  --large_theory_mode                     true
% 2.52/1.03  --prolific_symb_bound                   200
% 2.52/1.03  --lt_threshold                          2000
% 2.52/1.03  --clause_weak_htbl                      true
% 2.52/1.03  --gc_record_bc_elim                     false
% 2.52/1.03  
% 2.52/1.03  ------ Preprocessing Options
% 2.52/1.03  
% 2.52/1.03  --preprocessing_flag                    true
% 2.52/1.03  --time_out_prep_mult                    0.1
% 2.52/1.03  --splitting_mode                        input
% 2.52/1.03  --splitting_grd                         true
% 2.52/1.03  --splitting_cvd                         false
% 2.52/1.03  --splitting_cvd_svl                     false
% 2.52/1.03  --splitting_nvd                         32
% 2.52/1.03  --sub_typing                            true
% 2.52/1.03  --prep_gs_sim                           true
% 2.52/1.03  --prep_unflatten                        true
% 2.52/1.03  --prep_res_sim                          true
% 2.52/1.03  --prep_upred                            true
% 2.52/1.03  --prep_sem_filter                       exhaustive
% 2.52/1.03  --prep_sem_filter_out                   false
% 2.52/1.03  --pred_elim                             true
% 2.52/1.03  --res_sim_input                         true
% 2.52/1.03  --eq_ax_congr_red                       true
% 2.52/1.03  --pure_diseq_elim                       true
% 2.52/1.03  --brand_transform                       false
% 2.52/1.03  --non_eq_to_eq                          false
% 2.52/1.03  --prep_def_merge                        true
% 2.52/1.03  --prep_def_merge_prop_impl              false
% 2.52/1.03  --prep_def_merge_mbd                    true
% 2.52/1.03  --prep_def_merge_tr_red                 false
% 2.52/1.03  --prep_def_merge_tr_cl                  false
% 2.52/1.03  --smt_preprocessing                     true
% 2.52/1.03  --smt_ac_axioms                         fast
% 2.52/1.03  --preprocessed_out                      false
% 2.52/1.03  --preprocessed_stats                    false
% 2.52/1.03  
% 2.52/1.03  ------ Abstraction refinement Options
% 2.52/1.03  
% 2.52/1.03  --abstr_ref                             []
% 2.52/1.03  --abstr_ref_prep                        false
% 2.52/1.03  --abstr_ref_until_sat                   false
% 2.52/1.03  --abstr_ref_sig_restrict                funpre
% 2.52/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/1.03  --abstr_ref_under                       []
% 2.52/1.03  
% 2.52/1.03  ------ SAT Options
% 2.52/1.03  
% 2.52/1.03  --sat_mode                              false
% 2.52/1.03  --sat_fm_restart_options                ""
% 2.52/1.03  --sat_gr_def                            false
% 2.52/1.03  --sat_epr_types                         true
% 2.52/1.03  --sat_non_cyclic_types                  false
% 2.52/1.03  --sat_finite_models                     false
% 2.52/1.03  --sat_fm_lemmas                         false
% 2.52/1.03  --sat_fm_prep                           false
% 2.52/1.03  --sat_fm_uc_incr                        true
% 2.52/1.03  --sat_out_model                         small
% 2.52/1.03  --sat_out_clauses                       false
% 2.52/1.03  
% 2.52/1.03  ------ QBF Options
% 2.52/1.03  
% 2.52/1.03  --qbf_mode                              false
% 2.52/1.03  --qbf_elim_univ                         false
% 2.52/1.03  --qbf_dom_inst                          none
% 2.52/1.03  --qbf_dom_pre_inst                      false
% 2.52/1.03  --qbf_sk_in                             false
% 2.52/1.03  --qbf_pred_elim                         true
% 2.52/1.03  --qbf_split                             512
% 2.52/1.03  
% 2.52/1.03  ------ BMC1 Options
% 2.52/1.03  
% 2.52/1.03  --bmc1_incremental                      false
% 2.52/1.03  --bmc1_axioms                           reachable_all
% 2.52/1.03  --bmc1_min_bound                        0
% 2.52/1.03  --bmc1_max_bound                        -1
% 2.52/1.03  --bmc1_max_bound_default                -1
% 2.52/1.03  --bmc1_symbol_reachability              true
% 2.52/1.03  --bmc1_property_lemmas                  false
% 2.52/1.03  --bmc1_k_induction                      false
% 2.52/1.03  --bmc1_non_equiv_states                 false
% 2.52/1.03  --bmc1_deadlock                         false
% 2.52/1.03  --bmc1_ucm                              false
% 2.52/1.03  --bmc1_add_unsat_core                   none
% 2.52/1.03  --bmc1_unsat_core_children              false
% 2.52/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/1.03  --bmc1_out_stat                         full
% 2.52/1.03  --bmc1_ground_init                      false
% 2.52/1.03  --bmc1_pre_inst_next_state              false
% 2.52/1.03  --bmc1_pre_inst_state                   false
% 2.52/1.03  --bmc1_pre_inst_reach_state             false
% 2.52/1.03  --bmc1_out_unsat_core                   false
% 2.52/1.03  --bmc1_aig_witness_out                  false
% 2.52/1.03  --bmc1_verbose                          false
% 2.52/1.03  --bmc1_dump_clauses_tptp                false
% 2.52/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.52/1.03  --bmc1_dump_file                        -
% 2.52/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.52/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.52/1.03  --bmc1_ucm_extend_mode                  1
% 2.52/1.03  --bmc1_ucm_init_mode                    2
% 2.52/1.03  --bmc1_ucm_cone_mode                    none
% 2.52/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.52/1.03  --bmc1_ucm_relax_model                  4
% 2.52/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.52/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/1.03  --bmc1_ucm_layered_model                none
% 2.52/1.03  --bmc1_ucm_max_lemma_size               10
% 2.52/1.03  
% 2.52/1.03  ------ AIG Options
% 2.52/1.03  
% 2.52/1.03  --aig_mode                              false
% 2.52/1.03  
% 2.52/1.03  ------ Instantiation Options
% 2.52/1.03  
% 2.52/1.03  --instantiation_flag                    true
% 2.52/1.03  --inst_sos_flag                         false
% 2.52/1.03  --inst_sos_phase                        true
% 2.52/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/1.03  --inst_lit_sel_side                     none
% 2.52/1.03  --inst_solver_per_active                1400
% 2.52/1.03  --inst_solver_calls_frac                1.
% 2.52/1.03  --inst_passive_queue_type               priority_queues
% 2.52/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/1.03  --inst_passive_queues_freq              [25;2]
% 2.52/1.03  --inst_dismatching                      true
% 2.52/1.03  --inst_eager_unprocessed_to_passive     true
% 2.52/1.03  --inst_prop_sim_given                   true
% 2.52/1.03  --inst_prop_sim_new                     false
% 2.52/1.03  --inst_subs_new                         false
% 2.52/1.03  --inst_eq_res_simp                      false
% 2.52/1.03  --inst_subs_given                       false
% 2.52/1.03  --inst_orphan_elimination               true
% 2.52/1.03  --inst_learning_loop_flag               true
% 2.52/1.03  --inst_learning_start                   3000
% 2.52/1.03  --inst_learning_factor                  2
% 2.52/1.03  --inst_start_prop_sim_after_learn       3
% 2.52/1.03  --inst_sel_renew                        solver
% 2.52/1.03  --inst_lit_activity_flag                true
% 2.52/1.03  --inst_restr_to_given                   false
% 2.52/1.03  --inst_activity_threshold               500
% 2.52/1.03  --inst_out_proof                        true
% 2.52/1.03  
% 2.52/1.03  ------ Resolution Options
% 2.52/1.03  
% 2.52/1.03  --resolution_flag                       false
% 2.52/1.03  --res_lit_sel                           adaptive
% 2.52/1.03  --res_lit_sel_side                      none
% 2.52/1.03  --res_ordering                          kbo
% 2.52/1.03  --res_to_prop_solver                    active
% 2.52/1.03  --res_prop_simpl_new                    false
% 2.52/1.03  --res_prop_simpl_given                  true
% 2.52/1.03  --res_passive_queue_type                priority_queues
% 2.52/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/1.03  --res_passive_queues_freq               [15;5]
% 2.52/1.03  --res_forward_subs                      full
% 2.52/1.03  --res_backward_subs                     full
% 2.52/1.03  --res_forward_subs_resolution           true
% 2.52/1.03  --res_backward_subs_resolution          true
% 2.52/1.03  --res_orphan_elimination                true
% 2.52/1.03  --res_time_limit                        2.
% 2.52/1.03  --res_out_proof                         true
% 2.52/1.03  
% 2.52/1.03  ------ Superposition Options
% 2.52/1.03  
% 2.52/1.03  --superposition_flag                    true
% 2.52/1.03  --sup_passive_queue_type                priority_queues
% 2.52/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.52/1.03  --demod_completeness_check              fast
% 2.52/1.03  --demod_use_ground                      true
% 2.52/1.03  --sup_to_prop_solver                    passive
% 2.52/1.03  --sup_prop_simpl_new                    true
% 2.52/1.03  --sup_prop_simpl_given                  true
% 2.52/1.03  --sup_fun_splitting                     false
% 2.52/1.03  --sup_smt_interval                      50000
% 2.52/1.03  
% 2.52/1.03  ------ Superposition Simplification Setup
% 2.52/1.03  
% 2.52/1.03  --sup_indices_passive                   []
% 2.52/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.03  --sup_full_bw                           [BwDemod]
% 2.52/1.03  --sup_immed_triv                        [TrivRules]
% 2.52/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.03  --sup_immed_bw_main                     []
% 2.52/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/1.03  
% 2.52/1.03  ------ Combination Options
% 2.52/1.03  
% 2.52/1.03  --comb_res_mult                         3
% 2.52/1.03  --comb_sup_mult                         2
% 2.52/1.03  --comb_inst_mult                        10
% 2.52/1.03  
% 2.52/1.03  ------ Debug Options
% 2.52/1.03  
% 2.52/1.03  --dbg_backtrace                         false
% 2.52/1.03  --dbg_dump_prop_clauses                 false
% 2.52/1.03  --dbg_dump_prop_clauses_file            -
% 2.52/1.03  --dbg_out_stat                          false
% 2.52/1.03  
% 2.52/1.03  
% 2.52/1.03  
% 2.52/1.03  
% 2.52/1.03  ------ Proving...
% 2.52/1.03  
% 2.52/1.03  
% 2.52/1.03  % SZS status Theorem for theBenchmark.p
% 2.52/1.03  
% 2.52/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/1.03  
% 2.52/1.03  fof(f10,conjecture,(
% 2.52/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 2.52/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.03  
% 2.52/1.03  fof(f11,negated_conjecture,(
% 2.52/1.03    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 2.52/1.03    inference(negated_conjecture,[],[f10])).
% 2.52/1.03  
% 2.52/1.03  fof(f20,plain,(
% 2.52/1.03    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.52/1.03    inference(ennf_transformation,[],[f11])).
% 2.52/1.03  
% 2.52/1.03  fof(f21,plain,(
% 2.52/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.52/1.03    inference(flattening,[],[f20])).
% 2.52/1.03  
% 2.52/1.03  fof(f29,plain,(
% 2.52/1.03    ( ! [X2,X1] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v4_pre_topc(sK4,X2) & sK4 = X1 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X2))))) )),
% 2.52/1.03    introduced(choice_axiom,[])).
% 2.52/1.03  
% 2.52/1.03  fof(f28,plain,(
% 2.52/1.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) => (? [X3] : (~v4_pre_topc(X3,sK3) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & v4_pre_topc(X1,X0) & m1_pre_topc(sK3,X0))) )),
% 2.52/1.03    introduced(choice_axiom,[])).
% 2.52/1.03  
% 2.52/1.03  fof(f27,plain,(
% 2.52/1.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK2,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.52/1.03    introduced(choice_axiom,[])).
% 2.52/1.03  
% 2.52/1.03  fof(f26,plain,(
% 2.52/1.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK1) & m1_pre_topc(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 2.52/1.03    introduced(choice_axiom,[])).
% 2.52/1.03  
% 2.52/1.03  fof(f30,plain,(
% 2.52/1.03    (((~v4_pre_topc(sK4,sK3) & sK2 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & v4_pre_topc(sK2,sK1) & m1_pre_topc(sK3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 2.52/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f29,f28,f27,f26])).
% 2.52/1.03  
% 2.52/1.03  fof(f47,plain,(
% 2.52/1.03    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.52/1.03    inference(cnf_transformation,[],[f30])).
% 2.52/1.03  
% 2.52/1.03  fof(f7,axiom,(
% 2.52/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.52/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.03  
% 2.52/1.03  fof(f17,plain,(
% 2.52/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.52/1.03    inference(ennf_transformation,[],[f7])).
% 2.52/1.03  
% 2.52/1.03  fof(f37,plain,(
% 2.52/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.52/1.03    inference(cnf_transformation,[],[f17])).
% 2.52/1.03  
% 2.52/1.03  fof(f6,axiom,(
% 2.52/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.52/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.03  
% 2.52/1.03  fof(f16,plain,(
% 2.52/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.52/1.03    inference(ennf_transformation,[],[f6])).
% 2.52/1.03  
% 2.52/1.03  fof(f36,plain,(
% 2.52/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.52/1.03    inference(cnf_transformation,[],[f16])).
% 2.52/1.03  
% 2.52/1.03  fof(f8,axiom,(
% 2.52/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.52/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.03  
% 2.52/1.03  fof(f18,plain,(
% 2.52/1.03    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.52/1.03    inference(ennf_transformation,[],[f8])).
% 2.52/1.03  
% 2.52/1.03  fof(f38,plain,(
% 2.52/1.03    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.52/1.03    inference(cnf_transformation,[],[f18])).
% 2.52/1.03  
% 2.52/1.03  fof(f45,plain,(
% 2.52/1.03    m1_pre_topc(sK3,sK1)),
% 2.52/1.03    inference(cnf_transformation,[],[f30])).
% 2.52/1.03  
% 2.52/1.03  fof(f43,plain,(
% 2.52/1.03    l1_pre_topc(sK1)),
% 2.52/1.03    inference(cnf_transformation,[],[f30])).
% 2.52/1.03  
% 2.52/1.03  fof(f5,axiom,(
% 2.52/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.52/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.03  
% 2.52/1.03  fof(f12,plain,(
% 2.52/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.52/1.03    inference(unused_predicate_definition_removal,[],[f5])).
% 2.52/1.03  
% 2.52/1.03  fof(f15,plain,(
% 2.52/1.03    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.52/1.03    inference(ennf_transformation,[],[f12])).
% 2.52/1.03  
% 2.52/1.03  fof(f35,plain,(
% 2.52/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.52/1.03    inference(cnf_transformation,[],[f15])).
% 2.52/1.03  
% 2.52/1.03  fof(f1,axiom,(
% 2.52/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.52/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.03  
% 2.52/1.03  fof(f13,plain,(
% 2.52/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.52/1.03    inference(ennf_transformation,[],[f1])).
% 2.52/1.03  
% 2.52/1.03  fof(f31,plain,(
% 2.52/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.52/1.03    inference(cnf_transformation,[],[f13])).
% 2.52/1.03  
% 2.52/1.03  fof(f3,axiom,(
% 2.52/1.03    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.52/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.03  
% 2.52/1.03  fof(f33,plain,(
% 2.52/1.03    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.52/1.03    inference(cnf_transformation,[],[f3])).
% 2.52/1.03  
% 2.52/1.03  fof(f2,axiom,(
% 2.52/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 2.52/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.03  
% 2.52/1.03  fof(f32,plain,(
% 2.52/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.52/1.03    inference(cnf_transformation,[],[f2])).
% 2.52/1.03  
% 2.52/1.03  fof(f4,axiom,(
% 2.52/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.52/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.03  
% 2.52/1.03  fof(f14,plain,(
% 2.52/1.03    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.52/1.03    inference(ennf_transformation,[],[f4])).
% 2.52/1.03  
% 2.52/1.03  fof(f34,plain,(
% 2.52/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.52/1.03    inference(cnf_transformation,[],[f14])).
% 2.52/1.03  
% 2.52/1.03  fof(f9,axiom,(
% 2.52/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.52/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.03  
% 2.52/1.03  fof(f19,plain,(
% 2.52/1.03    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.52/1.03    inference(ennf_transformation,[],[f9])).
% 2.52/1.03  
% 2.52/1.03  fof(f22,plain,(
% 2.52/1.03    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.52/1.03    inference(nnf_transformation,[],[f19])).
% 2.52/1.03  
% 2.52/1.03  fof(f23,plain,(
% 2.52/1.03    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.52/1.03    inference(rectify,[],[f22])).
% 2.52/1.03  
% 2.52/1.03  fof(f24,plain,(
% 2.52/1.03    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.52/1.03    introduced(choice_axiom,[])).
% 2.52/1.03  
% 2.52/1.03  fof(f25,plain,(
% 2.52/1.03    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK0(X0,X1,X2),X0) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.52/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 2.52/1.03  
% 2.52/1.03  fof(f42,plain,(
% 2.52/1.03    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.52/1.03    inference(cnf_transformation,[],[f25])).
% 2.52/1.03  
% 2.52/1.03  fof(f50,plain,(
% 2.52/1.03    ( ! [X0,X3,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.52/1.03    inference(equality_resolution,[],[f42])).
% 2.52/1.03  
% 2.52/1.03  fof(f44,plain,(
% 2.52/1.03    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.52/1.03    inference(cnf_transformation,[],[f30])).
% 2.52/1.03  
% 2.52/1.03  fof(f48,plain,(
% 2.52/1.03    sK2 = sK4),
% 2.52/1.03    inference(cnf_transformation,[],[f30])).
% 2.52/1.03  
% 2.52/1.03  fof(f46,plain,(
% 2.52/1.03    v4_pre_topc(sK2,sK1)),
% 2.52/1.03    inference(cnf_transformation,[],[f30])).
% 2.52/1.03  
% 2.52/1.03  fof(f49,plain,(
% 2.52/1.03    ~v4_pre_topc(sK4,sK3)),
% 2.52/1.03    inference(cnf_transformation,[],[f30])).
% 2.52/1.03  
% 2.52/1.03  cnf(c_14,negated_conjecture,
% 2.52/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.52/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_636,plain,
% 2.52/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_6,plain,
% 2.52/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.52/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_5,plain,
% 2.52/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.52/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_205,plain,
% 2.52/1.03      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.52/1.03      inference(resolution,[status(thm)],[c_6,c_5]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_7,plain,
% 2.52/1.03      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.52/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_16,negated_conjecture,
% 2.52/1.03      ( m1_pre_topc(sK3,sK1) ),
% 2.52/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_219,plain,
% 2.52/1.03      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK1 != X0 | sK3 != X1 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_220,plain,
% 2.52/1.03      ( ~ l1_pre_topc(sK1) | l1_pre_topc(sK3) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_219]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_18,negated_conjecture,
% 2.52/1.03      ( l1_pre_topc(sK1) ),
% 2.52/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_222,plain,
% 2.52/1.03      ( l1_pre_topc(sK3) ),
% 2.52/1.03      inference(global_propositional_subsumption,
% 2.52/1.03                [status(thm)],
% 2.52/1.03                [c_220,c_18]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_341,plain,
% 2.52/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_205,c_222]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_342,plain,
% 2.52/1.03      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_341]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_656,plain,
% 2.52/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 2.52/1.03      inference(light_normalisation,[status(thm)],[c_636,c_342]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_4,plain,
% 2.52/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.52/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_0,plain,
% 2.52/1.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.52/1.03      inference(cnf_transformation,[],[f31]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_191,plain,
% 2.52/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_xboole_0(X0,X1) = X0 ),
% 2.52/1.03      inference(resolution,[status(thm)],[c_4,c_0]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_633,plain,
% 2.52/1.03      ( k3_xboole_0(X0,X1) = X0
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1002,plain,
% 2.52/1.03      ( k3_xboole_0(sK4,k2_struct_0(sK3)) = sK4 ),
% 2.52/1.03      inference(superposition,[status(thm)],[c_656,c_633]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_2,plain,
% 2.52/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.52/1.03      inference(cnf_transformation,[],[f33]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_639,plain,
% 2.52/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1,plain,
% 2.52/1.03      ( k2_subset_1(X0) = X0 ),
% 2.52/1.03      inference(cnf_transformation,[],[f32]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_659,plain,
% 2.52/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.52/1.03      inference(light_normalisation,[status(thm)],[c_639,c_1]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_3,plain,
% 2.52/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/1.03      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 2.52/1.03      inference(cnf_transformation,[],[f34]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_638,plain,
% 2.52/1.03      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 2.52/1.03      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1129,plain,
% 2.52/1.03      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 2.52/1.03      inference(superposition,[status(thm)],[c_659,c_638]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_8,plain,
% 2.52/1.03      ( ~ v4_pre_topc(X0,X1)
% 2.52/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
% 2.52/1.03      | ~ m1_pre_topc(X2,X1)
% 2.52/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.03      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 2.52/1.03      | ~ l1_pre_topc(X1) ),
% 2.52/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_230,plain,
% 2.52/1.03      ( ~ v4_pre_topc(X0,X1)
% 2.52/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
% 2.52/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.52/1.03      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 2.52/1.03      | ~ l1_pre_topc(X1)
% 2.52/1.03      | sK1 != X1
% 2.52/1.03      | sK3 != X2 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_231,plain,
% 2.52/1.03      ( ~ v4_pre_topc(X0,sK1)
% 2.52/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
% 2.52/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.03      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.52/1.03      | ~ l1_pre_topc(sK1) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_230]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_235,plain,
% 2.52/1.03      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.52/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
% 2.52/1.03      | ~ v4_pre_topc(X0,sK1) ),
% 2.52/1.03      inference(global_propositional_subsumption,
% 2.52/1.03                [status(thm)],
% 2.52/1.03                [c_231,c_18]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_236,plain,
% 2.52/1.03      ( ~ v4_pre_topc(X0,sK1)
% 2.52/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
% 2.52/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.52/1.03      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.52/1.03      inference(renaming,[status(thm)],[c_235]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_632,plain,
% 2.52/1.03      ( v4_pre_topc(X0,sK1) != iProver_top
% 2.52/1.03      | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3) = iProver_top
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.52/1.03      | m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_336,plain,
% 2.52/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.52/1.03      inference(resolution_lifted,[status(thm)],[c_205,c_18]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_337,plain,
% 2.52/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.52/1.03      inference(unflattening,[status(thm)],[c_336]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_691,plain,
% 2.52/1.03      ( v4_pre_topc(X0,sK1) != iProver_top
% 2.52/1.03      | v4_pre_topc(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),sK3) = iProver_top
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.52/1.03      | m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.52/1.03      inference(light_normalisation,[status(thm)],[c_632,c_337,c_342]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1599,plain,
% 2.52/1.03      ( v4_pre_topc(X0,sK1) != iProver_top
% 2.52/1.03      | v4_pre_topc(k3_xboole_0(X0,k2_struct_0(sK3)),sK3) = iProver_top
% 2.52/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.52/1.03      | m1_subset_1(k3_xboole_0(X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.52/1.03      inference(demodulation,[status(thm)],[c_1129,c_691]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1753,plain,
% 2.52/1.03      ( v4_pre_topc(k3_xboole_0(sK4,k2_struct_0(sK3)),sK3) = iProver_top
% 2.52/1.03      | v4_pre_topc(sK4,sK1) != iProver_top
% 2.52/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.52/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.52/1.03      inference(superposition,[status(thm)],[c_1002,c_1599]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_1768,plain,
% 2.52/1.03      ( v4_pre_topc(sK4,sK1) != iProver_top
% 2.52/1.03      | v4_pre_topc(sK4,sK3) = iProver_top
% 2.52/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.52/1.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.52/1.03      inference(light_normalisation,[status(thm)],[c_1753,c_1002]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_17,negated_conjecture,
% 2.52/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.52/1.03      inference(cnf_transformation,[],[f44]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_634,plain,
% 2.52/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_13,negated_conjecture,
% 2.52/1.03      ( sK2 = sK4 ),
% 2.52/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_653,plain,
% 2.52/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 2.52/1.03      inference(light_normalisation,[status(thm)],[c_634,c_13,c_337]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_15,negated_conjecture,
% 2.52/1.03      ( v4_pre_topc(sK2,sK1) ),
% 2.52/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_635,plain,
% 2.52/1.03      ( v4_pre_topc(sK2,sK1) = iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_648,plain,
% 2.52/1.03      ( v4_pre_topc(sK4,sK1) = iProver_top ),
% 2.52/1.03      inference(light_normalisation,[status(thm)],[c_635,c_13]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_12,negated_conjecture,
% 2.52/1.03      ( ~ v4_pre_topc(sK4,sK3) ),
% 2.52/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(c_24,plain,
% 2.52/1.03      ( v4_pre_topc(sK4,sK3) != iProver_top ),
% 2.52/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.52/1.03  
% 2.52/1.03  cnf(contradiction,plain,
% 2.52/1.03      ( $false ),
% 2.52/1.03      inference(minisat,[status(thm)],[c_1768,c_653,c_648,c_656,c_24]) ).
% 2.52/1.03  
% 2.52/1.03  
% 2.52/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/1.03  
% 2.52/1.03  ------                               Statistics
% 2.52/1.03  
% 2.52/1.03  ------ General
% 2.52/1.03  
% 2.52/1.03  abstr_ref_over_cycles:                  0
% 2.52/1.03  abstr_ref_under_cycles:                 0
% 2.52/1.03  gc_basic_clause_elim:                   0
% 2.52/1.03  forced_gc_time:                         0
% 2.52/1.03  parsing_time:                           0.015
% 2.52/1.03  unif_index_cands_time:                  0.
% 2.52/1.03  unif_index_add_time:                    0.
% 2.52/1.03  orderings_time:                         0.
% 2.52/1.03  out_proof_time:                         0.007
% 2.52/1.03  total_time:                             0.162
% 2.52/1.03  num_of_symbols:                         48
% 2.52/1.03  num_of_terms:                           1767
% 2.52/1.03  
% 2.52/1.03  ------ Preprocessing
% 2.52/1.03  
% 2.52/1.03  num_of_splits:                          0
% 2.52/1.03  num_of_split_atoms:                     0
% 2.52/1.03  num_of_reused_defs:                     0
% 2.52/1.03  num_eq_ax_congr_red:                    18
% 2.52/1.03  num_of_sem_filtered_clauses:            1
% 2.52/1.03  num_of_subtypes:                        0
% 2.52/1.03  monotx_restored_types:                  0
% 2.52/1.03  sat_num_of_epr_types:                   0
% 2.52/1.03  sat_num_of_non_cyclic_types:            0
% 2.52/1.03  sat_guarded_non_collapsed_types:        0
% 2.52/1.03  num_pure_diseq_elim:                    0
% 2.52/1.03  simp_replaced_by:                       0
% 2.52/1.03  res_preprocessed:                       83
% 2.52/1.03  prep_upred:                             0
% 2.52/1.03  prep_unflattend:                        12
% 2.52/1.03  smt_new_axioms:                         0
% 2.52/1.03  pred_elim_cands:                        2
% 2.52/1.03  pred_elim:                              4
% 2.52/1.03  pred_elim_cl:                           4
% 2.52/1.03  pred_elim_cycles:                       6
% 2.52/1.03  merged_defs:                            0
% 2.52/1.03  merged_defs_ncl:                        0
% 2.52/1.03  bin_hyper_res:                          0
% 2.52/1.03  prep_cycles:                            4
% 2.52/1.03  pred_elim_time:                         0.003
% 2.52/1.03  splitting_time:                         0.
% 2.52/1.03  sem_filter_time:                        0.
% 2.52/1.03  monotx_time:                            0.
% 2.52/1.03  subtype_inf_time:                       0.
% 2.52/1.03  
% 2.52/1.03  ------ Problem properties
% 2.52/1.03  
% 2.52/1.03  clauses:                                15
% 2.52/1.03  conjectures:                            5
% 2.52/1.03  epr:                                    3
% 2.52/1.03  horn:                                   15
% 2.52/1.03  ground:                                 7
% 2.52/1.03  unary:                                  9
% 2.52/1.03  binary:                                 2
% 2.52/1.03  lits:                                   26
% 2.52/1.03  lits_eq:                                7
% 2.52/1.03  fd_pure:                                0
% 2.52/1.03  fd_pseudo:                              0
% 2.52/1.03  fd_cond:                                0
% 2.52/1.03  fd_pseudo_cond:                         0
% 2.52/1.03  ac_symbols:                             0
% 2.52/1.03  
% 2.52/1.03  ------ Propositional Solver
% 2.52/1.03  
% 2.52/1.03  prop_solver_calls:                      26
% 2.52/1.03  prop_fast_solver_calls:                 433
% 2.52/1.03  smt_solver_calls:                       0
% 2.52/1.03  smt_fast_solver_calls:                  0
% 2.52/1.03  prop_num_of_clauses:                    640
% 2.52/1.03  prop_preprocess_simplified:             2484
% 2.52/1.03  prop_fo_subsumed:                       5
% 2.52/1.03  prop_solver_time:                       0.
% 2.52/1.03  smt_solver_time:                        0.
% 2.52/1.03  smt_fast_solver_time:                   0.
% 2.52/1.03  prop_fast_solver_time:                  0.
% 2.52/1.03  prop_unsat_core_time:                   0.
% 2.52/1.03  
% 2.52/1.03  ------ QBF
% 2.52/1.03  
% 2.52/1.03  qbf_q_res:                              0
% 2.52/1.03  qbf_num_tautologies:                    0
% 2.52/1.03  qbf_prep_cycles:                        0
% 2.52/1.03  
% 2.52/1.03  ------ BMC1
% 2.52/1.03  
% 2.52/1.03  bmc1_current_bound:                     -1
% 2.52/1.03  bmc1_last_solved_bound:                 -1
% 2.52/1.03  bmc1_unsat_core_size:                   -1
% 2.52/1.03  bmc1_unsat_core_parents_size:           -1
% 2.52/1.03  bmc1_merge_next_fun:                    0
% 2.52/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.52/1.03  
% 2.52/1.03  ------ Instantiation
% 2.52/1.03  
% 2.52/1.03  inst_num_of_clauses:                    208
% 2.52/1.03  inst_num_in_passive:                    58
% 2.52/1.03  inst_num_in_active:                     128
% 2.52/1.03  inst_num_in_unprocessed:                22
% 2.52/1.03  inst_num_of_loops:                      140
% 2.52/1.03  inst_num_of_learning_restarts:          0
% 2.52/1.03  inst_num_moves_active_passive:          9
% 2.52/1.03  inst_lit_activity:                      0
% 2.52/1.03  inst_lit_activity_moves:                0
% 2.52/1.03  inst_num_tautologies:                   0
% 2.52/1.03  inst_num_prop_implied:                  0
% 2.52/1.03  inst_num_existing_simplified:           0
% 2.52/1.03  inst_num_eq_res_simplified:             0
% 2.52/1.03  inst_num_child_elim:                    0
% 2.52/1.03  inst_num_of_dismatching_blockings:      73
% 2.52/1.03  inst_num_of_non_proper_insts:           167
% 2.52/1.03  inst_num_of_duplicates:                 0
% 2.52/1.03  inst_inst_num_from_inst_to_res:         0
% 2.52/1.03  inst_dismatching_checking_time:         0.
% 2.52/1.03  
% 2.52/1.03  ------ Resolution
% 2.52/1.03  
% 2.52/1.03  res_num_of_clauses:                     0
% 2.52/1.03  res_num_in_passive:                     0
% 2.52/1.03  res_num_in_active:                      0
% 2.52/1.03  res_num_of_loops:                       87
% 2.52/1.03  res_forward_subset_subsumed:            16
% 2.52/1.03  res_backward_subset_subsumed:           0
% 2.52/1.03  res_forward_subsumed:                   0
% 2.52/1.03  res_backward_subsumed:                  0
% 2.52/1.03  res_forward_subsumption_resolution:     0
% 2.52/1.03  res_backward_subsumption_resolution:    0
% 2.52/1.03  res_clause_to_clause_subsumption:       92
% 2.52/1.03  res_orphan_elimination:                 0
% 2.52/1.03  res_tautology_del:                      7
% 2.52/1.03  res_num_eq_res_simplified:              0
% 2.52/1.03  res_num_sel_changes:                    0
% 2.52/1.03  res_moves_from_active_to_pass:          0
% 2.52/1.03  
% 2.52/1.03  ------ Superposition
% 2.52/1.03  
% 2.52/1.03  sup_time_total:                         0.
% 2.52/1.03  sup_time_generating:                    0.
% 2.52/1.03  sup_time_sim_full:                      0.
% 2.52/1.03  sup_time_sim_immed:                     0.
% 2.52/1.03  
% 2.52/1.03  sup_num_of_clauses:                     28
% 2.52/1.03  sup_num_in_active:                      25
% 2.52/1.03  sup_num_in_passive:                     3
% 2.52/1.03  sup_num_of_loops:                       26
% 2.52/1.03  sup_fw_superposition:                   15
% 2.52/1.03  sup_bw_superposition:                   1
% 2.52/1.03  sup_immediate_simplified:               5
% 2.52/1.03  sup_given_eliminated:                   0
% 2.52/1.03  comparisons_done:                       0
% 2.52/1.03  comparisons_avoided:                    0
% 2.52/1.03  
% 2.52/1.03  ------ Simplifications
% 2.52/1.03  
% 2.52/1.03  
% 2.52/1.03  sim_fw_subset_subsumed:                 3
% 2.52/1.03  sim_bw_subset_subsumed:                 0
% 2.52/1.03  sim_fw_subsumed:                        0
% 2.52/1.03  sim_bw_subsumed:                        0
% 2.52/1.03  sim_fw_subsumption_res:                 0
% 2.52/1.03  sim_bw_subsumption_res:                 0
% 2.52/1.03  sim_tautology_del:                      0
% 2.52/1.03  sim_eq_tautology_del:                   0
% 2.52/1.03  sim_eq_res_simp:                        0
% 2.52/1.03  sim_fw_demodulated:                     2
% 2.52/1.03  sim_bw_demodulated:                     2
% 2.52/1.03  sim_light_normalised:                   9
% 2.52/1.03  sim_joinable_taut:                      0
% 2.52/1.03  sim_joinable_simp:                      0
% 2.52/1.03  sim_ac_normalised:                      0
% 2.52/1.03  sim_smt_subsumption:                    0
% 2.52/1.03  
%------------------------------------------------------------------------------
