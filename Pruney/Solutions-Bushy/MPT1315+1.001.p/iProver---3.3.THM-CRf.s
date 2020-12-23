%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1315+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:26 EST 2020

% Result     : Theorem 1.32s
% Output     : CNFRefutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 764 expanded)
%              Number of clauses        :   74 ( 242 expanded)
%              Number of leaves         :   16 ( 236 expanded)
%              Depth                    :   21
%              Number of atoms          :  344 (3722 expanded)
%              Number of equality atoms :  114 ( 770 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f32,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v4_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v4_pre_topc(sK4,X2)
        & sK4 = X1
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f33,plain,
    ( ~ v4_pre_topc(sK4,sK3)
    & sK2 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v4_pre_topc(sK2,sK1)
    & m1_pre_topc(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f32,f31,f30,f29])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f50,plain,(
    v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ~ v4_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_456,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_701,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_204,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_4,c_2])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_232,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_233,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_235,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_233,c_19])).

cnf(c_354,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_204,c_235])).

cnf(c_355,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_447,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_355])).

cnf(c_722,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_701,c_447])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k9_subset_1(X1_44,X0_44,X2_44) = k9_subset_1(X1_44,X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_697,plain,
    ( k9_subset_1(X0_44,X1_44,X2_44) = k9_subset_1(X0_44,X2_44,X1_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_1023,plain,
    ( k9_subset_1(k2_struct_0(sK3),X0_44,sK4) = k9_subset_1(k2_struct_0(sK3),sK4,X0_44) ),
    inference(superposition,[status(thm)],[c_722,c_697])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k9_subset_1(X1_44,X2_44,X0_44) = k3_xboole_0(X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_699,plain,
    ( k9_subset_1(X0_44,X1_44,X2_44) = k3_xboole_0(X1_44,X2_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_1097,plain,
    ( k9_subset_1(k2_struct_0(sK3),X0_44,sK4) = k3_xboole_0(X0_44,sK4) ),
    inference(superposition,[status(thm)],[c_722,c_699])).

cnf(c_1313,plain,
    ( k9_subset_1(k2_struct_0(sK3),sK4,X0_44) = k3_xboole_0(X0_44,sK4) ),
    inference(light_normalisation,[status(thm)],[c_1023,c_1097])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_243,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_244,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_248,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
    | ~ v4_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_244,c_19])).

cnf(c_249,plain,
    ( ~ v4_pre_topc(X0,sK1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_452,plain,
    ( ~ v4_pre_topc(X0_44,sK1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0_44,k2_struct_0(sK3)),sK3)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0_44,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_249])).

cnf(c_705,plain,
    ( v4_pre_topc(X0_44,sK1) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK3),X0_44,k2_struct_0(sK3)),sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0_44,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_349,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_204,c_19])).

cnf(c_350,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_448,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_350])).

cnf(c_765,plain,
    ( v4_pre_topc(X0_44,sK1) != iProver_top
    | v4_pre_topc(k9_subset_1(k2_struct_0(sK3),X0_44,k2_struct_0(sK3)),sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0_44,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_705,c_447,c_448])).

cnf(c_1317,plain,
    ( v4_pre_topc(k9_subset_1(k2_struct_0(sK3),sK4,k2_struct_0(sK3)),sK3) = iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top
    | m1_subset_1(k3_xboole_0(k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_765])).

cnf(c_1322,plain,
    ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK3),sK4),sK3) = iProver_top
    | v4_pre_topc(sK4,sK1) != iProver_top
    | m1_subset_1(k3_xboole_0(k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1317,c_1313])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_455,negated_conjecture,
    ( v4_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_702,plain,
    ( v4_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_14,negated_conjecture,
    ( sK2 = sK4 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_457,negated_conjecture,
    ( sK2 = sK4 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_711,plain,
    ( v4_pre_topc(sK4,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_702,c_457])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_454,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_703,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_725,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_703,c_448,c_457])).

cnf(c_3592,plain,
    ( m1_subset_1(k3_xboole_0(k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | v4_pre_topc(k3_xboole_0(k2_struct_0(sK3),sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1322,c_711,c_725])).

cnf(c_3593,plain,
    ( v4_pre_topc(k3_xboole_0(k2_struct_0(sK3),sK4),sK3) = iProver_top
    | m1_subset_1(k3_xboole_0(k2_struct_0(sK3),sK4),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3592])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k3_xboole_0(X0_44,X1_44) = X0_44 ),
    inference(subtyping,[status(esa)],[c_218])).

cnf(c_704,plain,
    ( k3_xboole_0(X0_44,X1_44) = X0_44
    | m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_1541,plain,
    ( k3_xboole_0(sK4,k2_struct_0(sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_722,c_704])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_462,plain,
    ( k3_xboole_0(X0_44,X1_44) = k3_xboole_0(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1098,plain,
    ( k9_subset_1(k2_struct_0(sK1),X0_44,sK4) = k3_xboole_0(X0_44,sK4) ),
    inference(superposition,[status(thm)],[c_725,c_699])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(k9_subset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_698,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(k9_subset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_1195,plain,
    ( m1_subset_1(k3_xboole_0(X0_44,sK4),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_698])).

cnf(c_1336,plain,
    ( m1_subset_1(k3_xboole_0(X0_44,sK4),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1195,c_725])).

cnf(c_1544,plain,
    ( k3_xboole_0(k3_xboole_0(X0_44,sK4),k2_struct_0(sK1)) = k3_xboole_0(X0_44,sK4) ),
    inference(superposition,[status(thm)],[c_1336,c_704])).

cnf(c_1991,plain,
    ( k3_xboole_0(k3_xboole_0(sK4,X0_44),k2_struct_0(sK1)) = k3_xboole_0(X0_44,sK4) ),
    inference(superposition,[status(thm)],[c_462,c_1544])).

cnf(c_2392,plain,
    ( k3_xboole_0(sK4,k2_struct_0(sK1)) = k3_xboole_0(k2_struct_0(sK3),sK4) ),
    inference(superposition,[status(thm)],[c_1541,c_1991])).

cnf(c_1542,plain,
    ( k3_xboole_0(sK4,k2_struct_0(sK1)) = sK4 ),
    inference(superposition,[status(thm)],[c_725,c_704])).

cnf(c_2400,plain,
    ( k3_xboole_0(k2_struct_0(sK3),sK4) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_2392,c_1542])).

cnf(c_3596,plain,
    ( v4_pre_topc(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3593,c_2400])).

cnf(c_13,negated_conjecture,
    ( ~ v4_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_458,negated_conjecture,
    ( ~ v4_pre_topc(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_700,plain,
    ( v4_pre_topc(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_3599,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3596,c_722,c_700])).


%------------------------------------------------------------------------------
