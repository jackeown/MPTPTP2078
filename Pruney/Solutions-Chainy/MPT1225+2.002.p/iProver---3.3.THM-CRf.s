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
% DateTime   : Thu Dec  3 12:13:33 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 460 expanded)
%              Number of clauses        :   68 ( 124 expanded)
%              Number of leaves         :   15 ( 137 expanded)
%              Depth                    :   16
%              Number of atoms          :  302 (2161 expanded)
%              Number of equality atoms :  121 ( 505 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
          & v4_pre_topc(X2,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2))
        & v4_pre_topc(sK2,X0)
        & v4_pre_topc(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2))
            & v4_pre_topc(X2,X0)
            & v4_pre_topc(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
                & v4_pre_topc(X2,X0)
                & v4_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2))
              & v4_pre_topc(X2,sK0)
              & v4_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    & v4_pre_topc(sK2,sK0)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33,f32,f31])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_594,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_593,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_599,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_595,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3170,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,k3_subset_1(X0,X2))) = k7_subset_1(X0,X1,k3_subset_1(X0,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_595])).

cnf(c_12692,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_3170])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_597,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1382,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_593,c_597])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_596,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2126,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_593,c_596])).

cnf(c_12725,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X0,sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12692,c_1382,c_2126])).

cnf(c_12977,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_594,c_12725])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_601,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2240,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK2,X0) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(superposition,[status(thm)],[c_594,c_601])).

cnf(c_2125,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_594,c_596])).

cnf(c_2770,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2240,c_2125])).

cnf(c_2780,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK1)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2770,c_2126])).

cnf(c_12999,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_12977,c_2780])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_598,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1887,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k7_subset_1(X0,X1,X2))) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_597])).

cnf(c_8150,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,X0))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(superposition,[status(thm)],[c_594,c_1887])).

cnf(c_8213,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8150,c_599])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_741,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_965,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_966,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_8386,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8213,c_22,c_966])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_591,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_8407,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK2,X0),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8386,c_591])).

cnf(c_13296,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12999,c_8407])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,negated_conjecture,
    ( v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK2 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_15])).

cnf(c_204,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_206,plain,
    ( k2_pre_topc(sK0,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_19,c_17])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_211,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_212,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_214,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_212,c_19,c_18])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_592,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_1015,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_214,c_592])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1468,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1015,c_21])).

cnf(c_1477,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_206,c_1468])).

cnf(c_1620,plain,
    ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1477,c_22])).

cnf(c_2373,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(sK1,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2125,c_1620])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_603,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4049,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k1_setfam_1(k2_tarski(sK1,sK2))
    | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2373,c_603])).

cnf(c_14,negated_conjecture,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_649,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_14,c_206,c_214])).

cnf(c_2374,plain,
    ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_2125,c_649])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13296,c_4049,c_2374])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.07  % Command    : iproveropt_run.sh %d %s
% 0.07/0.25  % Computer   : n014.cluster.edu
% 0.07/0.25  % Model      : x86_64 x86_64
% 0.07/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.25  % Memory     : 8042.1875MB
% 0.07/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.25  % CPULimit   : 60
% 0.07/0.25  % WCLimit    : 600
% 0.07/0.25  % DateTime   : Tue Dec  1 17:37:22 EST 2020
% 0.07/0.25  % CPUTime    : 
% 0.07/0.25  % Running in FOF mode
% 3.96/0.89  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/0.89  
% 3.96/0.89  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/0.89  
% 3.96/0.89  ------  iProver source info
% 3.96/0.89  
% 3.96/0.89  git: date: 2020-06-30 10:37:57 +0100
% 3.96/0.89  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/0.89  git: non_committed_changes: false
% 3.96/0.89  git: last_make_outside_of_git: false
% 3.96/0.89  
% 3.96/0.89  ------ 
% 3.96/0.89  
% 3.96/0.89  ------ Input Options
% 3.96/0.89  
% 3.96/0.89  --out_options                           all
% 3.96/0.89  --tptp_safe_out                         true
% 3.96/0.89  --problem_path                          ""
% 3.96/0.89  --include_path                          ""
% 3.96/0.89  --clausifier                            res/vclausify_rel
% 3.96/0.89  --clausifier_options                    --mode clausify
% 3.96/0.89  --stdin                                 false
% 3.96/0.89  --stats_out                             all
% 3.96/0.89  
% 3.96/0.89  ------ General Options
% 3.96/0.89  
% 3.96/0.89  --fof                                   false
% 3.96/0.89  --time_out_real                         305.
% 3.96/0.89  --time_out_virtual                      -1.
% 3.96/0.89  --symbol_type_check                     false
% 3.96/0.89  --clausify_out                          false
% 3.96/0.89  --sig_cnt_out                           false
% 3.96/0.89  --trig_cnt_out                          false
% 3.96/0.89  --trig_cnt_out_tolerance                1.
% 3.96/0.89  --trig_cnt_out_sk_spl                   false
% 3.96/0.89  --abstr_cl_out                          false
% 3.96/0.89  
% 3.96/0.89  ------ Global Options
% 3.96/0.89  
% 3.96/0.89  --schedule                              default
% 3.96/0.89  --add_important_lit                     false
% 3.96/0.89  --prop_solver_per_cl                    1000
% 3.96/0.89  --min_unsat_core                        false
% 3.96/0.89  --soft_assumptions                      false
% 3.96/0.89  --soft_lemma_size                       3
% 3.96/0.89  --prop_impl_unit_size                   0
% 3.96/0.89  --prop_impl_unit                        []
% 3.96/0.89  --share_sel_clauses                     true
% 3.96/0.89  --reset_solvers                         false
% 3.96/0.89  --bc_imp_inh                            [conj_cone]
% 3.96/0.89  --conj_cone_tolerance                   3.
% 3.96/0.89  --extra_neg_conj                        none
% 3.96/0.89  --large_theory_mode                     true
% 3.96/0.89  --prolific_symb_bound                   200
% 3.96/0.89  --lt_threshold                          2000
% 3.96/0.89  --clause_weak_htbl                      true
% 3.96/0.89  --gc_record_bc_elim                     false
% 3.96/0.89  
% 3.96/0.89  ------ Preprocessing Options
% 3.96/0.89  
% 3.96/0.89  --preprocessing_flag                    true
% 3.96/0.89  --time_out_prep_mult                    0.1
% 3.96/0.89  --splitting_mode                        input
% 3.96/0.89  --splitting_grd                         true
% 3.96/0.89  --splitting_cvd                         false
% 3.96/0.89  --splitting_cvd_svl                     false
% 3.96/0.89  --splitting_nvd                         32
% 3.96/0.89  --sub_typing                            true
% 3.96/0.89  --prep_gs_sim                           true
% 3.96/0.89  --prep_unflatten                        true
% 3.96/0.89  --prep_res_sim                          true
% 3.96/0.89  --prep_upred                            true
% 3.96/0.89  --prep_sem_filter                       exhaustive
% 3.96/0.89  --prep_sem_filter_out                   false
% 3.96/0.89  --pred_elim                             true
% 3.96/0.89  --res_sim_input                         true
% 3.96/0.89  --eq_ax_congr_red                       true
% 3.96/0.89  --pure_diseq_elim                       true
% 3.96/0.89  --brand_transform                       false
% 3.96/0.89  --non_eq_to_eq                          false
% 3.96/0.89  --prep_def_merge                        true
% 3.96/0.89  --prep_def_merge_prop_impl              false
% 3.96/0.89  --prep_def_merge_mbd                    true
% 3.96/0.89  --prep_def_merge_tr_red                 false
% 3.96/0.89  --prep_def_merge_tr_cl                  false
% 3.96/0.89  --smt_preprocessing                     true
% 3.96/0.89  --smt_ac_axioms                         fast
% 3.96/0.89  --preprocessed_out                      false
% 3.96/0.89  --preprocessed_stats                    false
% 3.96/0.89  
% 3.96/0.89  ------ Abstraction refinement Options
% 3.96/0.89  
% 3.96/0.89  --abstr_ref                             []
% 3.96/0.89  --abstr_ref_prep                        false
% 3.96/0.89  --abstr_ref_until_sat                   false
% 3.96/0.89  --abstr_ref_sig_restrict                funpre
% 3.96/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/0.89  --abstr_ref_under                       []
% 3.96/0.89  
% 3.96/0.89  ------ SAT Options
% 3.96/0.89  
% 3.96/0.89  --sat_mode                              false
% 3.96/0.89  --sat_fm_restart_options                ""
% 3.96/0.89  --sat_gr_def                            false
% 3.96/0.89  --sat_epr_types                         true
% 3.96/0.89  --sat_non_cyclic_types                  false
% 3.96/0.89  --sat_finite_models                     false
% 3.96/0.89  --sat_fm_lemmas                         false
% 3.96/0.89  --sat_fm_prep                           false
% 3.96/0.89  --sat_fm_uc_incr                        true
% 3.96/0.89  --sat_out_model                         small
% 3.96/0.89  --sat_out_clauses                       false
% 3.96/0.89  
% 3.96/0.89  ------ QBF Options
% 3.96/0.89  
% 3.96/0.89  --qbf_mode                              false
% 3.96/0.89  --qbf_elim_univ                         false
% 3.96/0.89  --qbf_dom_inst                          none
% 3.96/0.89  --qbf_dom_pre_inst                      false
% 3.96/0.89  --qbf_sk_in                             false
% 3.96/0.89  --qbf_pred_elim                         true
% 3.96/0.89  --qbf_split                             512
% 3.96/0.89  
% 3.96/0.89  ------ BMC1 Options
% 3.96/0.89  
% 3.96/0.89  --bmc1_incremental                      false
% 3.96/0.89  --bmc1_axioms                           reachable_all
% 3.96/0.89  --bmc1_min_bound                        0
% 3.96/0.89  --bmc1_max_bound                        -1
% 3.96/0.89  --bmc1_max_bound_default                -1
% 3.96/0.89  --bmc1_symbol_reachability              true
% 3.96/0.89  --bmc1_property_lemmas                  false
% 3.96/0.89  --bmc1_k_induction                      false
% 3.96/0.89  --bmc1_non_equiv_states                 false
% 3.96/0.89  --bmc1_deadlock                         false
% 3.96/0.89  --bmc1_ucm                              false
% 3.96/0.89  --bmc1_add_unsat_core                   none
% 3.96/0.89  --bmc1_unsat_core_children              false
% 3.96/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/0.89  --bmc1_out_stat                         full
% 3.96/0.89  --bmc1_ground_init                      false
% 3.96/0.89  --bmc1_pre_inst_next_state              false
% 3.96/0.89  --bmc1_pre_inst_state                   false
% 3.96/0.89  --bmc1_pre_inst_reach_state             false
% 3.96/0.89  --bmc1_out_unsat_core                   false
% 3.96/0.89  --bmc1_aig_witness_out                  false
% 3.96/0.89  --bmc1_verbose                          false
% 3.96/0.89  --bmc1_dump_clauses_tptp                false
% 3.96/0.89  --bmc1_dump_unsat_core_tptp             false
% 3.96/0.89  --bmc1_dump_file                        -
% 3.96/0.89  --bmc1_ucm_expand_uc_limit              128
% 3.96/0.89  --bmc1_ucm_n_expand_iterations          6
% 3.96/0.89  --bmc1_ucm_extend_mode                  1
% 3.96/0.89  --bmc1_ucm_init_mode                    2
% 3.96/0.89  --bmc1_ucm_cone_mode                    none
% 3.96/0.89  --bmc1_ucm_reduced_relation_type        0
% 3.96/0.89  --bmc1_ucm_relax_model                  4
% 3.96/0.89  --bmc1_ucm_full_tr_after_sat            true
% 3.96/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/0.89  --bmc1_ucm_layered_model                none
% 3.96/0.89  --bmc1_ucm_max_lemma_size               10
% 3.96/0.89  
% 3.96/0.89  ------ AIG Options
% 3.96/0.89  
% 3.96/0.89  --aig_mode                              false
% 3.96/0.89  
% 3.96/0.89  ------ Instantiation Options
% 3.96/0.89  
% 3.96/0.89  --instantiation_flag                    true
% 3.96/0.89  --inst_sos_flag                         false
% 3.96/0.89  --inst_sos_phase                        true
% 3.96/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/0.89  --inst_lit_sel_side                     num_symb
% 3.96/0.89  --inst_solver_per_active                1400
% 3.96/0.89  --inst_solver_calls_frac                1.
% 3.96/0.89  --inst_passive_queue_type               priority_queues
% 3.96/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/0.89  --inst_passive_queues_freq              [25;2]
% 3.96/0.89  --inst_dismatching                      true
% 3.96/0.89  --inst_eager_unprocessed_to_passive     true
% 3.96/0.89  --inst_prop_sim_given                   true
% 3.96/0.89  --inst_prop_sim_new                     false
% 3.96/0.89  --inst_subs_new                         false
% 3.96/0.89  --inst_eq_res_simp                      false
% 3.96/0.89  --inst_subs_given                       false
% 3.96/0.89  --inst_orphan_elimination               true
% 3.96/0.89  --inst_learning_loop_flag               true
% 3.96/0.89  --inst_learning_start                   3000
% 3.96/0.89  --inst_learning_factor                  2
% 3.96/0.89  --inst_start_prop_sim_after_learn       3
% 3.96/0.89  --inst_sel_renew                        solver
% 3.96/0.89  --inst_lit_activity_flag                true
% 3.96/0.89  --inst_restr_to_given                   false
% 3.96/0.89  --inst_activity_threshold               500
% 3.96/0.89  --inst_out_proof                        true
% 3.96/0.89  
% 3.96/0.89  ------ Resolution Options
% 3.96/0.89  
% 3.96/0.89  --resolution_flag                       true
% 3.96/0.89  --res_lit_sel                           adaptive
% 3.96/0.89  --res_lit_sel_side                      none
% 3.96/0.89  --res_ordering                          kbo
% 3.96/0.89  --res_to_prop_solver                    active
% 3.96/0.89  --res_prop_simpl_new                    false
% 3.96/0.89  --res_prop_simpl_given                  true
% 3.96/0.89  --res_passive_queue_type                priority_queues
% 3.96/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/0.89  --res_passive_queues_freq               [15;5]
% 3.96/0.89  --res_forward_subs                      full
% 3.96/0.89  --res_backward_subs                     full
% 3.96/0.89  --res_forward_subs_resolution           true
% 3.96/0.89  --res_backward_subs_resolution          true
% 3.96/0.89  --res_orphan_elimination                true
% 3.96/0.89  --res_time_limit                        2.
% 3.96/0.89  --res_out_proof                         true
% 3.96/0.89  
% 3.96/0.89  ------ Superposition Options
% 3.96/0.89  
% 3.96/0.89  --superposition_flag                    true
% 3.96/0.89  --sup_passive_queue_type                priority_queues
% 3.96/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/0.89  --sup_passive_queues_freq               [8;1;4]
% 3.96/0.89  --demod_completeness_check              fast
% 3.96/0.89  --demod_use_ground                      true
% 3.96/0.89  --sup_to_prop_solver                    passive
% 3.96/0.89  --sup_prop_simpl_new                    true
% 3.96/0.89  --sup_prop_simpl_given                  true
% 3.96/0.89  --sup_fun_splitting                     false
% 3.96/0.89  --sup_smt_interval                      50000
% 3.96/0.89  
% 3.96/0.89  ------ Superposition Simplification Setup
% 3.96/0.89  
% 3.96/0.89  --sup_indices_passive                   []
% 3.96/0.89  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.89  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.89  --sup_full_bw                           [BwDemod]
% 3.96/0.89  --sup_immed_triv                        [TrivRules]
% 3.96/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.89  --sup_immed_bw_main                     []
% 3.96/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.89  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/0.89  
% 3.96/0.89  ------ Combination Options
% 3.96/0.89  
% 3.96/0.89  --comb_res_mult                         3
% 3.96/0.89  --comb_sup_mult                         2
% 3.96/0.89  --comb_inst_mult                        10
% 3.96/0.89  
% 3.96/0.89  ------ Debug Options
% 3.96/0.89  
% 3.96/0.89  --dbg_backtrace                         false
% 3.96/0.89  --dbg_dump_prop_clauses                 false
% 3.96/0.89  --dbg_dump_prop_clauses_file            -
% 3.96/0.89  --dbg_out_stat                          false
% 3.96/0.89  ------ Parsing...
% 3.96/0.89  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/0.89  
% 3.96/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.96/0.89  
% 3.96/0.89  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/0.89  
% 3.96/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/0.89  ------ Proving...
% 3.96/0.89  ------ Problem Properties 
% 3.96/0.89  
% 3.96/0.89  
% 3.96/0.89  clauses                                 17
% 3.96/0.89  conjectures                             3
% 3.96/0.89  EPR                                     2
% 3.96/0.89  Horn                                    17
% 3.96/0.89  unary                                   8
% 3.96/0.89  binary                                  6
% 3.96/0.89  lits                                    29
% 3.96/0.89  lits eq                                 9
% 3.96/0.89  fd_pure                                 0
% 3.96/0.89  fd_pseudo                               0
% 3.96/0.89  fd_cond                                 0
% 3.96/0.89  fd_pseudo_cond                          1
% 3.96/0.89  AC symbols                              0
% 3.96/0.89  
% 3.96/0.89  ------ Schedule dynamic 5 is on 
% 3.96/0.89  
% 3.96/0.89  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.96/0.89  
% 3.96/0.89  
% 3.96/0.89  ------ 
% 3.96/0.89  Current options:
% 3.96/0.89  ------ 
% 3.96/0.89  
% 3.96/0.89  ------ Input Options
% 3.96/0.89  
% 3.96/0.89  --out_options                           all
% 3.96/0.89  --tptp_safe_out                         true
% 3.96/0.89  --problem_path                          ""
% 3.96/0.89  --include_path                          ""
% 3.96/0.89  --clausifier                            res/vclausify_rel
% 3.96/0.89  --clausifier_options                    --mode clausify
% 3.96/0.89  --stdin                                 false
% 3.96/0.89  --stats_out                             all
% 3.96/0.89  
% 3.96/0.89  ------ General Options
% 3.96/0.89  
% 3.96/0.89  --fof                                   false
% 3.96/0.89  --time_out_real                         305.
% 3.96/0.89  --time_out_virtual                      -1.
% 3.96/0.89  --symbol_type_check                     false
% 3.96/0.89  --clausify_out                          false
% 3.96/0.89  --sig_cnt_out                           false
% 3.96/0.89  --trig_cnt_out                          false
% 3.96/0.89  --trig_cnt_out_tolerance                1.
% 3.96/0.89  --trig_cnt_out_sk_spl                   false
% 3.96/0.89  --abstr_cl_out                          false
% 3.96/0.89  
% 3.96/0.89  ------ Global Options
% 3.96/0.89  
% 3.96/0.89  --schedule                              default
% 3.96/0.89  --add_important_lit                     false
% 3.96/0.89  --prop_solver_per_cl                    1000
% 3.96/0.89  --min_unsat_core                        false
% 3.96/0.89  --soft_assumptions                      false
% 3.96/0.89  --soft_lemma_size                       3
% 3.96/0.89  --prop_impl_unit_size                   0
% 3.96/0.89  --prop_impl_unit                        []
% 3.96/0.89  --share_sel_clauses                     true
% 3.96/0.89  --reset_solvers                         false
% 3.96/0.89  --bc_imp_inh                            [conj_cone]
% 3.96/0.89  --conj_cone_tolerance                   3.
% 3.96/0.89  --extra_neg_conj                        none
% 3.96/0.89  --large_theory_mode                     true
% 3.96/0.89  --prolific_symb_bound                   200
% 3.96/0.89  --lt_threshold                          2000
% 3.96/0.89  --clause_weak_htbl                      true
% 3.96/0.89  --gc_record_bc_elim                     false
% 3.96/0.89  
% 3.96/0.89  ------ Preprocessing Options
% 3.96/0.89  
% 3.96/0.89  --preprocessing_flag                    true
% 3.96/0.89  --time_out_prep_mult                    0.1
% 3.96/0.89  --splitting_mode                        input
% 3.96/0.89  --splitting_grd                         true
% 3.96/0.89  --splitting_cvd                         false
% 3.96/0.89  --splitting_cvd_svl                     false
% 3.96/0.89  --splitting_nvd                         32
% 3.96/0.89  --sub_typing                            true
% 3.96/0.89  --prep_gs_sim                           true
% 3.96/0.89  --prep_unflatten                        true
% 3.96/0.89  --prep_res_sim                          true
% 3.96/0.89  --prep_upred                            true
% 3.96/0.89  --prep_sem_filter                       exhaustive
% 3.96/0.89  --prep_sem_filter_out                   false
% 3.96/0.89  --pred_elim                             true
% 3.96/0.89  --res_sim_input                         true
% 3.96/0.89  --eq_ax_congr_red                       true
% 3.96/0.89  --pure_diseq_elim                       true
% 3.96/0.89  --brand_transform                       false
% 3.96/0.89  --non_eq_to_eq                          false
% 3.96/0.89  --prep_def_merge                        true
% 3.96/0.89  --prep_def_merge_prop_impl              false
% 3.96/0.89  --prep_def_merge_mbd                    true
% 3.96/0.89  --prep_def_merge_tr_red                 false
% 3.96/0.89  --prep_def_merge_tr_cl                  false
% 3.96/0.89  --smt_preprocessing                     true
% 3.96/0.89  --smt_ac_axioms                         fast
% 3.96/0.89  --preprocessed_out                      false
% 3.96/0.89  --preprocessed_stats                    false
% 3.96/0.89  
% 3.96/0.89  ------ Abstraction refinement Options
% 3.96/0.89  
% 3.96/0.89  --abstr_ref                             []
% 3.96/0.89  --abstr_ref_prep                        false
% 3.96/0.89  --abstr_ref_until_sat                   false
% 3.96/0.89  --abstr_ref_sig_restrict                funpre
% 3.96/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/0.89  --abstr_ref_under                       []
% 3.96/0.89  
% 3.96/0.89  ------ SAT Options
% 3.96/0.89  
% 3.96/0.89  --sat_mode                              false
% 3.96/0.89  --sat_fm_restart_options                ""
% 3.96/0.89  --sat_gr_def                            false
% 3.96/0.89  --sat_epr_types                         true
% 3.96/0.89  --sat_non_cyclic_types                  false
% 3.96/0.89  --sat_finite_models                     false
% 3.96/0.89  --sat_fm_lemmas                         false
% 3.96/0.89  --sat_fm_prep                           false
% 3.96/0.89  --sat_fm_uc_incr                        true
% 3.96/0.89  --sat_out_model                         small
% 3.96/0.89  --sat_out_clauses                       false
% 3.96/0.89  
% 3.96/0.89  ------ QBF Options
% 3.96/0.89  
% 3.96/0.89  --qbf_mode                              false
% 3.96/0.89  --qbf_elim_univ                         false
% 3.96/0.89  --qbf_dom_inst                          none
% 3.96/0.89  --qbf_dom_pre_inst                      false
% 3.96/0.89  --qbf_sk_in                             false
% 3.96/0.89  --qbf_pred_elim                         true
% 3.96/0.89  --qbf_split                             512
% 3.96/0.89  
% 3.96/0.89  ------ BMC1 Options
% 3.96/0.89  
% 3.96/0.89  --bmc1_incremental                      false
% 3.96/0.89  --bmc1_axioms                           reachable_all
% 3.96/0.89  --bmc1_min_bound                        0
% 3.96/0.89  --bmc1_max_bound                        -1
% 3.96/0.89  --bmc1_max_bound_default                -1
% 3.96/0.89  --bmc1_symbol_reachability              true
% 3.96/0.89  --bmc1_property_lemmas                  false
% 3.96/0.89  --bmc1_k_induction                      false
% 3.96/0.89  --bmc1_non_equiv_states                 false
% 3.96/0.89  --bmc1_deadlock                         false
% 3.96/0.89  --bmc1_ucm                              false
% 3.96/0.89  --bmc1_add_unsat_core                   none
% 3.96/0.89  --bmc1_unsat_core_children              false
% 3.96/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/0.89  --bmc1_out_stat                         full
% 3.96/0.89  --bmc1_ground_init                      false
% 3.96/0.89  --bmc1_pre_inst_next_state              false
% 3.96/0.89  --bmc1_pre_inst_state                   false
% 3.96/0.89  --bmc1_pre_inst_reach_state             false
% 3.96/0.89  --bmc1_out_unsat_core                   false
% 3.96/0.89  --bmc1_aig_witness_out                  false
% 3.96/0.89  --bmc1_verbose                          false
% 3.96/0.89  --bmc1_dump_clauses_tptp                false
% 3.96/0.89  --bmc1_dump_unsat_core_tptp             false
% 3.96/0.89  --bmc1_dump_file                        -
% 3.96/0.89  --bmc1_ucm_expand_uc_limit              128
% 3.96/0.89  --bmc1_ucm_n_expand_iterations          6
% 3.96/0.89  --bmc1_ucm_extend_mode                  1
% 3.96/0.89  --bmc1_ucm_init_mode                    2
% 3.96/0.89  --bmc1_ucm_cone_mode                    none
% 3.96/0.89  --bmc1_ucm_reduced_relation_type        0
% 3.96/0.89  --bmc1_ucm_relax_model                  4
% 3.96/0.89  --bmc1_ucm_full_tr_after_sat            true
% 3.96/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/0.89  --bmc1_ucm_layered_model                none
% 3.96/0.89  --bmc1_ucm_max_lemma_size               10
% 3.96/0.89  
% 3.96/0.89  ------ AIG Options
% 3.96/0.89  
% 3.96/0.89  --aig_mode                              false
% 3.96/0.89  
% 3.96/0.89  ------ Instantiation Options
% 3.96/0.89  
% 3.96/0.89  --instantiation_flag                    true
% 3.96/0.89  --inst_sos_flag                         false
% 3.96/0.89  --inst_sos_phase                        true
% 3.96/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/0.89  --inst_lit_sel_side                     none
% 3.96/0.89  --inst_solver_per_active                1400
% 3.96/0.89  --inst_solver_calls_frac                1.
% 3.96/0.89  --inst_passive_queue_type               priority_queues
% 3.96/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/0.89  --inst_passive_queues_freq              [25;2]
% 3.96/0.89  --inst_dismatching                      true
% 3.96/0.89  --inst_eager_unprocessed_to_passive     true
% 3.96/0.89  --inst_prop_sim_given                   true
% 3.96/0.89  --inst_prop_sim_new                     false
% 3.96/0.89  --inst_subs_new                         false
% 3.96/0.89  --inst_eq_res_simp                      false
% 3.96/0.89  --inst_subs_given                       false
% 3.96/0.89  --inst_orphan_elimination               true
% 3.96/0.89  --inst_learning_loop_flag               true
% 3.96/0.89  --inst_learning_start                   3000
% 3.96/0.89  --inst_learning_factor                  2
% 3.96/0.89  --inst_start_prop_sim_after_learn       3
% 3.96/0.89  --inst_sel_renew                        solver
% 3.96/0.89  --inst_lit_activity_flag                true
% 3.96/0.89  --inst_restr_to_given                   false
% 3.96/0.89  --inst_activity_threshold               500
% 3.96/0.89  --inst_out_proof                        true
% 3.96/0.89  
% 3.96/0.89  ------ Resolution Options
% 3.96/0.89  
% 3.96/0.89  --resolution_flag                       false
% 3.96/0.89  --res_lit_sel                           adaptive
% 3.96/0.89  --res_lit_sel_side                      none
% 3.96/0.89  --res_ordering                          kbo
% 3.96/0.89  --res_to_prop_solver                    active
% 3.96/0.89  --res_prop_simpl_new                    false
% 3.96/0.89  --res_prop_simpl_given                  true
% 3.96/0.89  --res_passive_queue_type                priority_queues
% 3.96/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/0.89  --res_passive_queues_freq               [15;5]
% 3.96/0.89  --res_forward_subs                      full
% 3.96/0.89  --res_backward_subs                     full
% 3.96/0.89  --res_forward_subs_resolution           true
% 3.96/0.89  --res_backward_subs_resolution          true
% 3.96/0.89  --res_orphan_elimination                true
% 3.96/0.89  --res_time_limit                        2.
% 3.96/0.89  --res_out_proof                         true
% 3.96/0.89  
% 3.96/0.89  ------ Superposition Options
% 3.96/0.89  
% 3.96/0.89  --superposition_flag                    true
% 3.96/0.89  --sup_passive_queue_type                priority_queues
% 3.96/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/0.89  --sup_passive_queues_freq               [8;1;4]
% 3.96/0.89  --demod_completeness_check              fast
% 3.96/0.89  --demod_use_ground                      true
% 3.96/0.89  --sup_to_prop_solver                    passive
% 3.96/0.89  --sup_prop_simpl_new                    true
% 3.96/0.89  --sup_prop_simpl_given                  true
% 3.96/0.89  --sup_fun_splitting                     false
% 3.96/0.89  --sup_smt_interval                      50000
% 3.96/0.89  
% 3.96/0.89  ------ Superposition Simplification Setup
% 3.96/0.89  
% 3.96/0.89  --sup_indices_passive                   []
% 3.96/0.89  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.89  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.89  --sup_full_bw                           [BwDemod]
% 3.96/0.89  --sup_immed_triv                        [TrivRules]
% 3.96/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.89  --sup_immed_bw_main                     []
% 3.96/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.89  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/0.89  
% 3.96/0.89  ------ Combination Options
% 3.96/0.89  
% 3.96/0.89  --comb_res_mult                         3
% 3.96/0.89  --comb_sup_mult                         2
% 3.96/0.89  --comb_inst_mult                        10
% 3.96/0.89  
% 3.96/0.89  ------ Debug Options
% 3.96/0.89  
% 3.96/0.89  --dbg_backtrace                         false
% 3.96/0.89  --dbg_dump_prop_clauses                 false
% 3.96/0.89  --dbg_dump_prop_clauses_file            -
% 3.96/0.89  --dbg_out_stat                          false
% 3.96/0.89  
% 3.96/0.89  
% 3.96/0.89  
% 3.96/0.89  
% 3.96/0.89  ------ Proving...
% 3.96/0.89  
% 3.96/0.89  
% 3.96/0.89  % SZS status Theorem for theBenchmark.p
% 3.96/0.89  
% 3.96/0.89  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/0.89  
% 3.96/0.89  fof(f14,conjecture,(
% 3.96/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f15,negated_conjecture,(
% 3.96/0.89    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 3.96/0.89    inference(negated_conjecture,[],[f14])).
% 3.96/0.89  
% 3.96/0.89  fof(f27,plain,(
% 3.96/0.89    ? [X0] : (? [X1] : (? [X2] : ((k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) & (v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.96/0.89    inference(ennf_transformation,[],[f15])).
% 3.96/0.89  
% 3.96/0.89  fof(f28,plain,(
% 3.96/0.89    ? [X0] : (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.96/0.89    inference(flattening,[],[f27])).
% 3.96/0.89  
% 3.96/0.89  fof(f33,plain,(
% 3.96/0.89    ( ! [X0,X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)) & v4_pre_topc(sK2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.96/0.89    introduced(choice_axiom,[])).
% 3.96/0.89  
% 3.96/0.89  fof(f32,plain,(
% 3.96/0.89    ( ! [X0] : (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.96/0.89    introduced(choice_axiom,[])).
% 3.96/0.89  
% 3.96/0.89  fof(f31,plain,(
% 3.96/0.89    ? [X0] : (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) & v4_pre_topc(X2,sK0) & v4_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.96/0.89    introduced(choice_axiom,[])).
% 3.96/0.89  
% 3.96/0.89  fof(f34,plain,(
% 3.96/0.89    ((k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) & v4_pre_topc(sK2,sK0) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.96/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f33,f32,f31])).
% 3.96/0.89  
% 3.96/0.89  fof(f52,plain,(
% 3.96/0.89    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.89    inference(cnf_transformation,[],[f34])).
% 3.96/0.89  
% 3.96/0.89  fof(f51,plain,(
% 3.96/0.89    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.89    inference(cnf_transformation,[],[f34])).
% 3.96/0.89  
% 3.96/0.89  fof(f5,axiom,(
% 3.96/0.89    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f18,plain,(
% 3.96/0.89    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.89    inference(ennf_transformation,[],[f5])).
% 3.96/0.89  
% 3.96/0.89  fof(f41,plain,(
% 3.96/0.89    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.89    inference(cnf_transformation,[],[f18])).
% 3.96/0.89  
% 3.96/0.89  fof(f9,axiom,(
% 3.96/0.89    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f22,plain,(
% 3.96/0.89    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.89    inference(ennf_transformation,[],[f9])).
% 3.96/0.89  
% 3.96/0.89  fof(f45,plain,(
% 3.96/0.89    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.89    inference(cnf_transformation,[],[f22])).
% 3.96/0.89  
% 3.96/0.89  fof(f7,axiom,(
% 3.96/0.89    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f20,plain,(
% 3.96/0.89    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.89    inference(ennf_transformation,[],[f7])).
% 3.96/0.89  
% 3.96/0.89  fof(f43,plain,(
% 3.96/0.89    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.89    inference(cnf_transformation,[],[f20])).
% 3.96/0.89  
% 3.96/0.89  fof(f8,axiom,(
% 3.96/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f21,plain,(
% 3.96/0.89    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.96/0.89    inference(ennf_transformation,[],[f8])).
% 3.96/0.89  
% 3.96/0.89  fof(f44,plain,(
% 3.96/0.89    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.96/0.89    inference(cnf_transformation,[],[f21])).
% 3.96/0.89  
% 3.96/0.89  fof(f10,axiom,(
% 3.96/0.89    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f46,plain,(
% 3.96/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.96/0.89    inference(cnf_transformation,[],[f10])).
% 3.96/0.89  
% 3.96/0.89  fof(f56,plain,(
% 3.96/0.89    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.96/0.89    inference(definition_unfolding,[],[f44,f46])).
% 3.96/0.89  
% 3.96/0.89  fof(f2,axiom,(
% 3.96/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f17,plain,(
% 3.96/0.89    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.96/0.89    inference(ennf_transformation,[],[f2])).
% 3.96/0.89  
% 3.96/0.89  fof(f38,plain,(
% 3.96/0.89    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.96/0.89    inference(cnf_transformation,[],[f17])).
% 3.96/0.89  
% 3.96/0.89  fof(f6,axiom,(
% 3.96/0.89    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f19,plain,(
% 3.96/0.89    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.89    inference(ennf_transformation,[],[f6])).
% 3.96/0.89  
% 3.96/0.89  fof(f42,plain,(
% 3.96/0.89    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.89    inference(cnf_transformation,[],[f19])).
% 3.96/0.89  
% 3.96/0.89  fof(f11,axiom,(
% 3.96/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f23,plain,(
% 3.96/0.89    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.89    inference(ennf_transformation,[],[f11])).
% 3.96/0.89  
% 3.96/0.89  fof(f47,plain,(
% 3.96/0.89    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.89    inference(cnf_transformation,[],[f23])).
% 3.96/0.89  
% 3.96/0.89  fof(f50,plain,(
% 3.96/0.89    l1_pre_topc(sK0)),
% 3.96/0.89    inference(cnf_transformation,[],[f34])).
% 3.96/0.89  
% 3.96/0.89  fof(f13,axiom,(
% 3.96/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f16,plain,(
% 3.96/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 3.96/0.89    inference(pure_predicate_removal,[],[f13])).
% 3.96/0.89  
% 3.96/0.89  fof(f25,plain,(
% 3.96/0.89    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.89    inference(ennf_transformation,[],[f16])).
% 3.96/0.89  
% 3.96/0.89  fof(f26,plain,(
% 3.96/0.89    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.89    inference(flattening,[],[f25])).
% 3.96/0.89  
% 3.96/0.89  fof(f49,plain,(
% 3.96/0.89    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.89    inference(cnf_transformation,[],[f26])).
% 3.96/0.89  
% 3.96/0.89  fof(f54,plain,(
% 3.96/0.89    v4_pre_topc(sK2,sK0)),
% 3.96/0.89    inference(cnf_transformation,[],[f34])).
% 3.96/0.89  
% 3.96/0.89  fof(f53,plain,(
% 3.96/0.89    v4_pre_topc(sK1,sK0)),
% 3.96/0.89    inference(cnf_transformation,[],[f34])).
% 3.96/0.89  
% 3.96/0.89  fof(f12,axiom,(
% 3.96/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f24,plain,(
% 3.96/0.89    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.89    inference(ennf_transformation,[],[f12])).
% 3.96/0.89  
% 3.96/0.89  fof(f48,plain,(
% 3.96/0.89    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.89    inference(cnf_transformation,[],[f24])).
% 3.96/0.89  
% 3.96/0.89  fof(f1,axiom,(
% 3.96/0.89    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.96/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.96/0.89  
% 3.96/0.89  fof(f29,plain,(
% 3.96/0.89    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.96/0.89    inference(nnf_transformation,[],[f1])).
% 3.96/0.89  
% 3.96/0.89  fof(f30,plain,(
% 3.96/0.89    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.96/0.89    inference(flattening,[],[f29])).
% 3.96/0.89  
% 3.96/0.89  fof(f37,plain,(
% 3.96/0.89    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.96/0.89    inference(cnf_transformation,[],[f30])).
% 3.96/0.89  
% 3.96/0.89  fof(f55,plain,(
% 3.96/0.89    k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 3.96/0.89    inference(cnf_transformation,[],[f34])).
% 3.96/0.89  
% 3.96/0.89  cnf(c_17,negated_conjecture,
% 3.96/0.89      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.96/0.89      inference(cnf_transformation,[],[f52]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_594,plain,
% 3.96/0.89      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_18,negated_conjecture,
% 3.96/0.89      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.96/0.89      inference(cnf_transformation,[],[f51]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_593,plain,
% 3.96/0.89      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_6,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.89      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.96/0.89      inference(cnf_transformation,[],[f41]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_599,plain,
% 3.96/0.89      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.96/0.89      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_10,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.89      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.96/0.89      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 3.96/0.89      inference(cnf_transformation,[],[f45]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_595,plain,
% 3.96/0.89      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 3.96/0.89      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.96/0.89      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_3170,plain,
% 3.96/0.89      ( k9_subset_1(X0,X1,k3_subset_1(X0,k3_subset_1(X0,X2))) = k7_subset_1(X0,X1,k3_subset_1(X0,X2))
% 3.96/0.89      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.96/0.89      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_599,c_595]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_12692,plain,
% 3.96/0.89      ( k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1))
% 3.96/0.89      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_593,c_3170]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_8,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.89      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.96/0.89      inference(cnf_transformation,[],[f43]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_597,plain,
% 3.96/0.89      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.96/0.89      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_1382,plain,
% 3.96/0.89      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_593,c_597]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_9,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.89      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.96/0.89      inference(cnf_transformation,[],[f56]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_596,plain,
% 3.96/0.89      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 3.96/0.89      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_2126,plain,
% 3.96/0.89      ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1)) ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_593,c_596]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_12725,plain,
% 3.96/0.89      ( k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X0,sK1))
% 3.96/0.89      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.96/0.89      inference(light_normalisation,
% 3.96/0.89                [status(thm)],
% 3.96/0.89                [c_12692,c_1382,c_2126]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_12977,plain,
% 3.96/0.89      ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_594,c_12725]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_3,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.89      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 3.96/0.89      inference(cnf_transformation,[],[f38]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_601,plain,
% 3.96/0.89      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 3.96/0.89      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_2240,plain,
% 3.96/0.89      ( k9_subset_1(u1_struct_0(sK0),sK2,X0) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_594,c_601]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_2125,plain,
% 3.96/0.89      ( k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_594,c_596]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_2770,plain,
% 3.96/0.89      ( k9_subset_1(u1_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2)) ),
% 3.96/0.89      inference(light_normalisation,[status(thm)],[c_2240,c_2125]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_2780,plain,
% 3.96/0.89      ( k1_setfam_1(k2_tarski(sK2,sK1)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_2770,c_2126]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_12999,plain,
% 3.96/0.89      ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.96/0.89      inference(light_normalisation,[status(thm)],[c_12977,c_2780]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_7,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.96/0.89      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 3.96/0.89      inference(cnf_transformation,[],[f42]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_598,plain,
% 3.96/0.89      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.96/0.89      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_1887,plain,
% 3.96/0.89      ( k3_subset_1(X0,k3_subset_1(X0,k7_subset_1(X0,X1,X2))) = k7_subset_1(X0,X1,X2)
% 3.96/0.89      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_598,c_597]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_8150,plain,
% 3.96/0.89      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,X0))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_594,c_1887]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_8213,plain,
% 3.96/0.89      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.96/0.89      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_8150,c_599]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_22,plain,
% 3.96/0.89      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_741,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.96/0.89      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.96/0.89      inference(instantiation,[status(thm)],[c_7]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_965,plain,
% 3.96/0.89      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.96/0.89      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.96/0.89      inference(instantiation,[status(thm)],[c_741]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_966,plain,
% 3.96/0.89      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.96/0.89      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_8386,plain,
% 3.96/0.89      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.96/0.89      inference(global_propositional_subsumption,
% 3.96/0.89                [status(thm)],
% 3.96/0.89                [c_8213,c_22,c_966]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_11,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.96/0.89      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.96/0.89      | ~ l1_pre_topc(X1) ),
% 3.96/0.89      inference(cnf_transformation,[],[f47]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_19,negated_conjecture,
% 3.96/0.89      ( l1_pre_topc(sK0) ),
% 3.96/0.89      inference(cnf_transformation,[],[f50]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_236,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.96/0.89      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.96/0.89      | sK0 != X1 ),
% 3.96/0.89      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_237,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.96/0.89      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 3.96/0.89      inference(unflattening,[status(thm)],[c_236]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_591,plain,
% 3.96/0.89      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.96/0.89      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_8407,plain,
% 3.96/0.89      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK2,X0),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK2,X0))) = iProver_top ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_8386,c_591]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_13296,plain,
% 3.96/0.89      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))) = iProver_top ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_12999,c_8407]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_13,plain,
% 3.96/0.89      ( ~ v4_pre_topc(X0,X1)
% 3.96/0.89      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.96/0.89      | ~ l1_pre_topc(X1)
% 3.96/0.89      | k2_pre_topc(X1,X0) = X0 ),
% 3.96/0.89      inference(cnf_transformation,[],[f49]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_15,negated_conjecture,
% 3.96/0.89      ( v4_pre_topc(sK2,sK0) ),
% 3.96/0.89      inference(cnf_transformation,[],[f54]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_203,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.96/0.89      | ~ l1_pre_topc(X1)
% 3.96/0.89      | k2_pre_topc(X1,X0) = X0
% 3.96/0.89      | sK2 != X0
% 3.96/0.89      | sK0 != X1 ),
% 3.96/0.89      inference(resolution_lifted,[status(thm)],[c_13,c_15]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_204,plain,
% 3.96/0.89      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.96/0.89      | ~ l1_pre_topc(sK0)
% 3.96/0.89      | k2_pre_topc(sK0,sK2) = sK2 ),
% 3.96/0.89      inference(unflattening,[status(thm)],[c_203]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_206,plain,
% 3.96/0.89      ( k2_pre_topc(sK0,sK2) = sK2 ),
% 3.96/0.89      inference(global_propositional_subsumption,
% 3.96/0.89                [status(thm)],
% 3.96/0.89                [c_204,c_19,c_17]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_16,negated_conjecture,
% 3.96/0.89      ( v4_pre_topc(sK1,sK0) ),
% 3.96/0.89      inference(cnf_transformation,[],[f53]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_211,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.96/0.89      | ~ l1_pre_topc(X1)
% 3.96/0.89      | k2_pre_topc(X1,X0) = X0
% 3.96/0.89      | sK1 != X0
% 3.96/0.89      | sK0 != X1 ),
% 3.96/0.89      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_212,plain,
% 3.96/0.89      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.96/0.89      | ~ l1_pre_topc(sK0)
% 3.96/0.89      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.96/0.89      inference(unflattening,[status(thm)],[c_211]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_214,plain,
% 3.96/0.89      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.96/0.89      inference(global_propositional_subsumption,
% 3.96/0.89                [status(thm)],
% 3.96/0.89                [c_212,c_19,c_18]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_12,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.96/0.89      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.96/0.89      | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
% 3.96/0.89      | ~ l1_pre_topc(X1) ),
% 3.96/0.89      inference(cnf_transformation,[],[f48]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_221,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.96/0.89      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.96/0.89      | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
% 3.96/0.89      | sK0 != X1 ),
% 3.96/0.89      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_222,plain,
% 3.96/0.89      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.96/0.89      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.96/0.89      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))) ),
% 3.96/0.89      inference(unflattening,[status(thm)],[c_221]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_592,plain,
% 3.96/0.89      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.96/0.89      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.96/0.89      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))) = iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_1015,plain,
% 3.96/0.89      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.96/0.89      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.96/0.89      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))) = iProver_top ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_214,c_592]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_21,plain,
% 3.96/0.89      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_1468,plain,
% 3.96/0.89      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.96/0.89      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X0)),k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))) = iProver_top ),
% 3.96/0.89      inference(global_propositional_subsumption,
% 3.96/0.89                [status(thm)],
% 3.96/0.89                [c_1015,c_21]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_1477,plain,
% 3.96/0.89      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.96/0.89      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = iProver_top ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_206,c_1468]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_1620,plain,
% 3.96/0.89      ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = iProver_top ),
% 3.96/0.89      inference(global_propositional_subsumption,
% 3.96/0.89                [status(thm)],
% 3.96/0.89                [c_1477,c_22]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_2373,plain,
% 3.96/0.89      ( r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(sK1,sK2))) = iProver_top ),
% 3.96/0.89      inference(demodulation,[status(thm)],[c_2125,c_1620]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_0,plain,
% 3.96/0.89      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.96/0.89      inference(cnf_transformation,[],[f37]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_603,plain,
% 3.96/0.89      ( X0 = X1
% 3.96/0.89      | r1_tarski(X0,X1) != iProver_top
% 3.96/0.89      | r1_tarski(X1,X0) != iProver_top ),
% 3.96/0.89      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_4049,plain,
% 3.96/0.89      ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) = k1_setfam_1(k2_tarski(sK1,sK2))
% 3.96/0.89      | r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2)))) != iProver_top ),
% 3.96/0.89      inference(superposition,[status(thm)],[c_2373,c_603]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_14,negated_conjecture,
% 3.96/0.89      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 3.96/0.89      inference(cnf_transformation,[],[f55]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_649,plain,
% 3.96/0.89      ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 3.96/0.89      inference(light_normalisation,[status(thm)],[c_14,c_206,c_214]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(c_2374,plain,
% 3.96/0.89      ( k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 3.96/0.89      inference(demodulation,[status(thm)],[c_2125,c_649]) ).
% 3.96/0.89  
% 3.96/0.89  cnf(contradiction,plain,
% 3.96/0.89      ( $false ),
% 3.96/0.89      inference(minisat,[status(thm)],[c_13296,c_4049,c_2374]) ).
% 3.96/0.89  
% 3.96/0.89  
% 3.96/0.89  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/0.89  
% 3.96/0.89  ------                               Statistics
% 3.96/0.89  
% 3.96/0.89  ------ General
% 3.96/0.89  
% 3.96/0.89  abstr_ref_over_cycles:                  0
% 3.96/0.89  abstr_ref_under_cycles:                 0
% 3.96/0.89  gc_basic_clause_elim:                   0
% 3.96/0.89  forced_gc_time:                         0
% 3.96/0.89  parsing_time:                           0.009
% 3.96/0.89  unif_index_cands_time:                  0.
% 3.96/0.89  unif_index_add_time:                    0.
% 3.96/0.89  orderings_time:                         0.
% 3.96/0.89  out_proof_time:                         0.01
% 3.96/0.89  total_time:                             0.444
% 3.96/0.89  num_of_symbols:                         47
% 3.96/0.89  num_of_terms:                           21319
% 3.96/0.89  
% 3.96/0.89  ------ Preprocessing
% 3.96/0.89  
% 3.96/0.89  num_of_splits:                          0
% 3.96/0.89  num_of_split_atoms:                     0
% 3.96/0.89  num_of_reused_defs:                     0
% 3.96/0.89  num_eq_ax_congr_red:                    21
% 3.96/0.89  num_of_sem_filtered_clauses:            1
% 3.96/0.89  num_of_subtypes:                        0
% 3.96/0.89  monotx_restored_types:                  0
% 3.96/0.89  sat_num_of_epr_types:                   0
% 3.96/0.89  sat_num_of_non_cyclic_types:            0
% 3.96/0.89  sat_guarded_non_collapsed_types:        0
% 3.96/0.89  num_pure_diseq_elim:                    0
% 3.96/0.89  simp_replaced_by:                       0
% 3.96/0.89  res_preprocessed:                       91
% 3.96/0.89  prep_upred:                             0
% 3.96/0.89  prep_unflattend:                        6
% 3.96/0.89  smt_new_axioms:                         0
% 3.96/0.89  pred_elim_cands:                        2
% 3.96/0.89  pred_elim:                              2
% 3.96/0.89  pred_elim_cl:                           2
% 3.96/0.89  pred_elim_cycles:                       4
% 3.96/0.89  merged_defs:                            0
% 3.96/0.89  merged_defs_ncl:                        0
% 3.96/0.89  bin_hyper_res:                          0
% 3.96/0.89  prep_cycles:                            4
% 3.96/0.89  pred_elim_time:                         0.001
% 3.96/0.89  splitting_time:                         0.
% 3.96/0.89  sem_filter_time:                        0.
% 3.96/0.89  monotx_time:                            0.
% 3.96/0.89  subtype_inf_time:                       0.
% 3.96/0.89  
% 3.96/0.89  ------ Problem properties
% 3.96/0.89  
% 3.96/0.89  clauses:                                17
% 3.96/0.89  conjectures:                            3
% 3.96/0.89  epr:                                    2
% 3.96/0.89  horn:                                   17
% 3.96/0.89  ground:                                 5
% 3.96/0.89  unary:                                  8
% 3.96/0.89  binary:                                 6
% 3.96/0.89  lits:                                   29
% 3.96/0.89  lits_eq:                                9
% 3.96/0.89  fd_pure:                                0
% 3.96/0.89  fd_pseudo:                              0
% 3.96/0.89  fd_cond:                                0
% 3.96/0.89  fd_pseudo_cond:                         1
% 3.96/0.89  ac_symbols:                             0
% 3.96/0.89  
% 3.96/0.89  ------ Propositional Solver
% 3.96/0.89  
% 3.96/0.89  prop_solver_calls:                      29
% 3.96/0.89  prop_fast_solver_calls:                 807
% 3.96/0.89  smt_solver_calls:                       0
% 3.96/0.89  smt_fast_solver_calls:                  0
% 3.96/0.89  prop_num_of_clauses:                    6138
% 3.96/0.89  prop_preprocess_simplified:             10649
% 3.96/0.89  prop_fo_subsumed:                       51
% 3.96/0.89  prop_solver_time:                       0.
% 3.96/0.89  smt_solver_time:                        0.
% 3.96/0.89  smt_fast_solver_time:                   0.
% 3.96/0.89  prop_fast_solver_time:                  0.
% 3.96/0.89  prop_unsat_core_time:                   0.001
% 3.96/0.89  
% 3.96/0.89  ------ QBF
% 3.96/0.89  
% 3.96/0.89  qbf_q_res:                              0
% 3.96/0.89  qbf_num_tautologies:                    0
% 3.96/0.89  qbf_prep_cycles:                        0
% 3.96/0.89  
% 3.96/0.89  ------ BMC1
% 3.96/0.89  
% 3.96/0.89  bmc1_current_bound:                     -1
% 3.96/0.89  bmc1_last_solved_bound:                 -1
% 3.96/0.89  bmc1_unsat_core_size:                   -1
% 3.96/0.89  bmc1_unsat_core_parents_size:           -1
% 3.96/0.89  bmc1_merge_next_fun:                    0
% 3.96/0.89  bmc1_unsat_core_clauses_time:           0.
% 3.96/0.89  
% 3.96/0.89  ------ Instantiation
% 3.96/0.89  
% 3.96/0.89  inst_num_of_clauses:                    1420
% 3.96/0.89  inst_num_in_passive:                    56
% 3.96/0.89  inst_num_in_active:                     936
% 3.96/0.89  inst_num_in_unprocessed:                428
% 3.96/0.89  inst_num_of_loops:                      970
% 3.96/0.89  inst_num_of_learning_restarts:          0
% 3.96/0.89  inst_num_moves_active_passive:          33
% 3.96/0.89  inst_lit_activity:                      0
% 3.96/0.89  inst_lit_activity_moves:                1
% 3.96/0.89  inst_num_tautologies:                   0
% 3.96/0.89  inst_num_prop_implied:                  0
% 3.96/0.89  inst_num_existing_simplified:           0
% 3.96/0.89  inst_num_eq_res_simplified:             0
% 3.96/0.89  inst_num_child_elim:                    0
% 3.96/0.89  inst_num_of_dismatching_blockings:      446
% 3.96/0.89  inst_num_of_non_proper_insts:           1042
% 3.96/0.89  inst_num_of_duplicates:                 0
% 3.96/0.89  inst_inst_num_from_inst_to_res:         0
% 3.96/0.89  inst_dismatching_checking_time:         0.
% 3.96/0.89  
% 3.96/0.89  ------ Resolution
% 3.96/0.89  
% 3.96/0.89  res_num_of_clauses:                     0
% 3.96/0.89  res_num_in_passive:                     0
% 3.96/0.89  res_num_in_active:                      0
% 3.96/0.89  res_num_of_loops:                       95
% 3.96/0.89  res_forward_subset_subsumed:            89
% 3.96/0.89  res_backward_subset_subsumed:           0
% 3.96/0.89  res_forward_subsumed:                   0
% 3.96/0.89  res_backward_subsumed:                  0
% 3.96/0.89  res_forward_subsumption_resolution:     0
% 3.96/0.89  res_backward_subsumption_resolution:    0
% 3.96/0.89  res_clause_to_clause_subsumption:       2315
% 3.96/0.89  res_orphan_elimination:                 0
% 3.96/0.89  res_tautology_del:                      22
% 3.96/0.89  res_num_eq_res_simplified:              0
% 3.96/0.89  res_num_sel_changes:                    0
% 3.96/0.89  res_moves_from_active_to_pass:          0
% 3.96/0.89  
% 3.96/0.89  ------ Superposition
% 3.96/0.89  
% 3.96/0.89  sup_time_total:                         0.
% 3.96/0.89  sup_time_generating:                    0.
% 3.96/0.89  sup_time_sim_full:                      0.
% 3.96/0.89  sup_time_sim_immed:                     0.
% 3.96/0.89  
% 3.96/0.89  sup_num_of_clauses:                     562
% 3.96/0.89  sup_num_in_active:                      177
% 3.96/0.89  sup_num_in_passive:                     385
% 3.96/0.89  sup_num_of_loops:                       193
% 3.96/0.89  sup_fw_superposition:                   524
% 3.96/0.89  sup_bw_superposition:                   433
% 3.96/0.89  sup_immediate_simplified:               258
% 3.96/0.89  sup_given_eliminated:                   1
% 3.96/0.89  comparisons_done:                       0
% 3.96/0.89  comparisons_avoided:                    0
% 3.96/0.89  
% 3.96/0.89  ------ Simplifications
% 3.96/0.89  
% 3.96/0.89  
% 3.96/0.89  sim_fw_subset_subsumed:                 16
% 3.96/0.89  sim_bw_subset_subsumed:                 1
% 3.96/0.89  sim_fw_subsumed:                        39
% 3.96/0.89  sim_bw_subsumed:                        0
% 3.96/0.89  sim_fw_subsumption_res:                 2
% 3.96/0.89  sim_bw_subsumption_res:                 0
% 3.96/0.89  sim_tautology_del:                      2
% 3.96/0.89  sim_eq_tautology_del:                   55
% 3.96/0.89  sim_eq_res_simp:                        0
% 3.96/0.89  sim_fw_demodulated:                     88
% 3.96/0.89  sim_bw_demodulated:                     30
% 3.96/0.89  sim_light_normalised:                   204
% 3.96/0.89  sim_joinable_taut:                      0
% 3.96/0.89  sim_joinable_simp:                      0
% 3.96/0.89  sim_ac_normalised:                      0
% 3.96/0.89  sim_smt_subsumption:                    0
% 3.96/0.89  
%------------------------------------------------------------------------------
