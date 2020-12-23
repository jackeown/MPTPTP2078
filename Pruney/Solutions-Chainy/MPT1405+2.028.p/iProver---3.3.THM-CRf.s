%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:52 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 433 expanded)
%              Number of clauses        :   78 ( 139 expanded)
%              Number of leaves         :   15 (  99 expanded)
%              Depth                    :   19
%              Number of atoms          :  380 (1462 expanded)
%              Number of equality atoms :   97 ( 165 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m2_connsp_2(k2_struct_0(X0),X0,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f39,f38])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_1(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_tops_1(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_tops_1(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f35])).

fof(f53,plain,(
    ! [X0] :
      ( v1_tops_1(sK0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_995,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_996,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1854,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_996])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_998,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1010,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_998,c_3])).

cnf(c_14,plain,
    ( ~ v1_tops_1(X0,X1)
    | v1_tops_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_368,plain,
    ( ~ v1_tops_1(X0,X1)
    | v1_tops_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_369,plain,
    ( ~ v1_tops_1(X0,sK1)
    | v1_tops_1(X1,sK1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_991,plain,
    ( v1_tops_1(X0,sK1) != iProver_top
    | v1_tops_1(X1,sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_1583,plain,
    ( v1_tops_1(X0,sK1) != iProver_top
    | v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_991])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1144,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1145,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1144])).

cnf(c_4049,plain,
    ( v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top
    | v1_tops_1(X0,sK1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1583,c_1145])).

cnf(c_4050,plain,
    ( v1_tops_1(X0,sK1) != iProver_top
    | v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4049])).

cnf(c_4058,plain,
    ( v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top
    | v1_tops_1(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1854,c_4050])).

cnf(c_22,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( v1_tops_1(sK0(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_38,plain,
    ( v1_tops_1(sK0(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_40,plain,
    ( v1_tops_1(sK0(sK1),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_12,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_354,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_355,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_993,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_1855,plain,
    ( r1_tarski(sK0(sK1),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_996])).

cnf(c_4059,plain,
    ( v1_tops_1(sK0(sK1),sK1) != iProver_top
    | v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_4050])).

cnf(c_4299,plain,
    ( v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4058,c_22,c_40,c_4059])).

cnf(c_10,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_387,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_388,plain,
    ( ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_990,plain,
    ( k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
    | v1_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_1498,plain,
    ( k2_pre_topc(sK1,u1_struct_0(sK1)) = k2_struct_0(sK1)
    | v1_tops_1(u1_struct_0(sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_990])).

cnf(c_4306,plain,
    ( k2_pre_topc(sK1,u1_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_4299,c_1498])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_988,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_1418,plain,
    ( r1_tarski(u1_struct_0(sK1),k2_pre_topc(sK1,u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_988])).

cnf(c_4889,plain,
    ( r1_tarski(u1_struct_0(sK1),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4306,c_1418])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1000,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2175,plain,
    ( r1_tarski(u1_struct_0(sK1),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1854,c_1000])).

cnf(c_5073,plain,
    ( r1_tarski(sK2,k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4889,c_2175])).

cnf(c_1496,plain,
    ( k2_pre_topc(sK1,sK0(sK1)) = k2_struct_0(sK1)
    | v1_tops_1(sK0(sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_990])).

cnf(c_36,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_39,plain,
    ( v1_tops_1(sK0(sK1),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1111,plain,
    ( ~ v1_tops_1(sK0(sK1),sK1)
    | ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,sK0(sK1)) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_1839,plain,
    ( k2_pre_topc(sK1,sK0(sK1)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1496,c_19,c_36,c_39,c_1111])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_987,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_1845,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_987])).

cnf(c_17,negated_conjecture,
    ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_301,plain,
    ( m2_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_302,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_306,plain,
    ( ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m2_connsp_2(X0,sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_19])).

cnf(c_307,plain,
    ( m2_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
    | k2_struct_0(sK1) != X0
    | sK2 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_307])).

cnf(c_338,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_340,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_18])).

cnf(c_994,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_13,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_269,plain,
    ( ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_270,plain,
    ( ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_33,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_272,plain,
    ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_20,c_19,c_33])).

cnf(c_1037,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK2,k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_994,c_272])).

cnf(c_35,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_37,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5073,c_1845,c_1037,c_37,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:16:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.03/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/0.98  
% 3.03/0.98  ------  iProver source info
% 3.03/0.98  
% 3.03/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.03/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/0.98  git: non_committed_changes: false
% 3.03/0.98  git: last_make_outside_of_git: false
% 3.03/0.98  
% 3.03/0.98  ------ 
% 3.03/0.98  
% 3.03/0.98  ------ Input Options
% 3.03/0.98  
% 3.03/0.98  --out_options                           all
% 3.03/0.98  --tptp_safe_out                         true
% 3.03/0.98  --problem_path                          ""
% 3.03/0.98  --include_path                          ""
% 3.03/0.98  --clausifier                            res/vclausify_rel
% 3.03/0.98  --clausifier_options                    --mode clausify
% 3.03/0.98  --stdin                                 false
% 3.03/0.98  --stats_out                             all
% 3.03/0.98  
% 3.03/0.98  ------ General Options
% 3.03/0.98  
% 3.03/0.98  --fof                                   false
% 3.03/0.98  --time_out_real                         305.
% 3.03/0.98  --time_out_virtual                      -1.
% 3.03/0.98  --symbol_type_check                     false
% 3.03/0.98  --clausify_out                          false
% 3.03/0.98  --sig_cnt_out                           false
% 3.03/0.98  --trig_cnt_out                          false
% 3.03/0.98  --trig_cnt_out_tolerance                1.
% 3.03/0.98  --trig_cnt_out_sk_spl                   false
% 3.03/0.98  --abstr_cl_out                          false
% 3.03/0.98  
% 3.03/0.98  ------ Global Options
% 3.03/0.98  
% 3.03/0.98  --schedule                              default
% 3.03/0.98  --add_important_lit                     false
% 3.03/0.98  --prop_solver_per_cl                    1000
% 3.03/0.98  --min_unsat_core                        false
% 3.03/0.98  --soft_assumptions                      false
% 3.03/0.98  --soft_lemma_size                       3
% 3.03/0.98  --prop_impl_unit_size                   0
% 3.03/0.98  --prop_impl_unit                        []
% 3.03/0.98  --share_sel_clauses                     true
% 3.03/0.98  --reset_solvers                         false
% 3.03/0.98  --bc_imp_inh                            [conj_cone]
% 3.03/0.98  --conj_cone_tolerance                   3.
% 3.03/0.98  --extra_neg_conj                        none
% 3.03/0.98  --large_theory_mode                     true
% 3.03/0.98  --prolific_symb_bound                   200
% 3.03/0.98  --lt_threshold                          2000
% 3.03/0.98  --clause_weak_htbl                      true
% 3.03/0.98  --gc_record_bc_elim                     false
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing Options
% 3.03/0.98  
% 3.03/0.98  --preprocessing_flag                    true
% 3.03/0.98  --time_out_prep_mult                    0.1
% 3.03/0.98  --splitting_mode                        input
% 3.03/0.98  --splitting_grd                         true
% 3.03/0.98  --splitting_cvd                         false
% 3.03/0.98  --splitting_cvd_svl                     false
% 3.03/0.98  --splitting_nvd                         32
% 3.03/0.98  --sub_typing                            true
% 3.03/0.98  --prep_gs_sim                           true
% 3.03/0.98  --prep_unflatten                        true
% 3.03/0.98  --prep_res_sim                          true
% 3.03/0.98  --prep_upred                            true
% 3.03/0.98  --prep_sem_filter                       exhaustive
% 3.03/0.98  --prep_sem_filter_out                   false
% 3.03/0.98  --pred_elim                             true
% 3.03/0.98  --res_sim_input                         true
% 3.03/0.98  --eq_ax_congr_red                       true
% 3.03/0.98  --pure_diseq_elim                       true
% 3.03/0.98  --brand_transform                       false
% 3.03/0.98  --non_eq_to_eq                          false
% 3.03/0.98  --prep_def_merge                        true
% 3.03/0.98  --prep_def_merge_prop_impl              false
% 3.03/0.98  --prep_def_merge_mbd                    true
% 3.03/0.98  --prep_def_merge_tr_red                 false
% 3.03/0.98  --prep_def_merge_tr_cl                  false
% 3.03/0.98  --smt_preprocessing                     true
% 3.03/0.98  --smt_ac_axioms                         fast
% 3.03/0.98  --preprocessed_out                      false
% 3.03/0.98  --preprocessed_stats                    false
% 3.03/0.98  
% 3.03/0.98  ------ Abstraction refinement Options
% 3.03/0.98  
% 3.03/0.98  --abstr_ref                             []
% 3.03/0.98  --abstr_ref_prep                        false
% 3.03/0.98  --abstr_ref_until_sat                   false
% 3.03/0.98  --abstr_ref_sig_restrict                funpre
% 3.03/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.98  --abstr_ref_under                       []
% 3.03/0.98  
% 3.03/0.98  ------ SAT Options
% 3.03/0.98  
% 3.03/0.98  --sat_mode                              false
% 3.03/0.98  --sat_fm_restart_options                ""
% 3.03/0.98  --sat_gr_def                            false
% 3.03/0.98  --sat_epr_types                         true
% 3.03/0.98  --sat_non_cyclic_types                  false
% 3.03/0.98  --sat_finite_models                     false
% 3.03/0.98  --sat_fm_lemmas                         false
% 3.03/0.98  --sat_fm_prep                           false
% 3.03/0.98  --sat_fm_uc_incr                        true
% 3.03/0.98  --sat_out_model                         small
% 3.03/0.98  --sat_out_clauses                       false
% 3.03/0.98  
% 3.03/0.98  ------ QBF Options
% 3.03/0.98  
% 3.03/0.98  --qbf_mode                              false
% 3.03/0.98  --qbf_elim_univ                         false
% 3.03/0.98  --qbf_dom_inst                          none
% 3.03/0.98  --qbf_dom_pre_inst                      false
% 3.03/0.98  --qbf_sk_in                             false
% 3.03/0.98  --qbf_pred_elim                         true
% 3.03/0.98  --qbf_split                             512
% 3.03/0.98  
% 3.03/0.98  ------ BMC1 Options
% 3.03/0.98  
% 3.03/0.98  --bmc1_incremental                      false
% 3.03/0.98  --bmc1_axioms                           reachable_all
% 3.03/0.98  --bmc1_min_bound                        0
% 3.03/0.98  --bmc1_max_bound                        -1
% 3.03/0.98  --bmc1_max_bound_default                -1
% 3.03/0.98  --bmc1_symbol_reachability              true
% 3.03/0.98  --bmc1_property_lemmas                  false
% 3.03/0.98  --bmc1_k_induction                      false
% 3.03/0.98  --bmc1_non_equiv_states                 false
% 3.03/0.98  --bmc1_deadlock                         false
% 3.03/0.98  --bmc1_ucm                              false
% 3.03/0.98  --bmc1_add_unsat_core                   none
% 3.03/0.98  --bmc1_unsat_core_children              false
% 3.03/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.98  --bmc1_out_stat                         full
% 3.03/0.98  --bmc1_ground_init                      false
% 3.03/0.98  --bmc1_pre_inst_next_state              false
% 3.03/0.98  --bmc1_pre_inst_state                   false
% 3.03/0.98  --bmc1_pre_inst_reach_state             false
% 3.03/0.98  --bmc1_out_unsat_core                   false
% 3.03/0.98  --bmc1_aig_witness_out                  false
% 3.03/0.98  --bmc1_verbose                          false
% 3.03/0.98  --bmc1_dump_clauses_tptp                false
% 3.03/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.98  --bmc1_dump_file                        -
% 3.03/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.98  --bmc1_ucm_extend_mode                  1
% 3.03/0.98  --bmc1_ucm_init_mode                    2
% 3.03/0.98  --bmc1_ucm_cone_mode                    none
% 3.03/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.98  --bmc1_ucm_relax_model                  4
% 3.03/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.98  --bmc1_ucm_layered_model                none
% 3.03/0.98  --bmc1_ucm_max_lemma_size               10
% 3.03/0.98  
% 3.03/0.98  ------ AIG Options
% 3.03/0.98  
% 3.03/0.98  --aig_mode                              false
% 3.03/0.98  
% 3.03/0.98  ------ Instantiation Options
% 3.03/0.98  
% 3.03/0.98  --instantiation_flag                    true
% 3.03/0.98  --inst_sos_flag                         false
% 3.03/0.98  --inst_sos_phase                        true
% 3.03/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.98  --inst_lit_sel_side                     num_symb
% 3.03/0.98  --inst_solver_per_active                1400
% 3.03/0.98  --inst_solver_calls_frac                1.
% 3.03/0.98  --inst_passive_queue_type               priority_queues
% 3.03/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.98  --inst_passive_queues_freq              [25;2]
% 3.03/0.98  --inst_dismatching                      true
% 3.03/0.98  --inst_eager_unprocessed_to_passive     true
% 3.03/0.98  --inst_prop_sim_given                   true
% 3.03/0.98  --inst_prop_sim_new                     false
% 3.03/0.98  --inst_subs_new                         false
% 3.03/0.98  --inst_eq_res_simp                      false
% 3.03/0.98  --inst_subs_given                       false
% 3.03/0.98  --inst_orphan_elimination               true
% 3.03/0.98  --inst_learning_loop_flag               true
% 3.03/0.98  --inst_learning_start                   3000
% 3.03/0.98  --inst_learning_factor                  2
% 3.03/0.98  --inst_start_prop_sim_after_learn       3
% 3.03/0.98  --inst_sel_renew                        solver
% 3.03/0.98  --inst_lit_activity_flag                true
% 3.03/0.98  --inst_restr_to_given                   false
% 3.03/0.98  --inst_activity_threshold               500
% 3.03/0.98  --inst_out_proof                        true
% 3.03/0.98  
% 3.03/0.98  ------ Resolution Options
% 3.03/0.98  
% 3.03/0.98  --resolution_flag                       true
% 3.03/0.98  --res_lit_sel                           adaptive
% 3.03/0.98  --res_lit_sel_side                      none
% 3.03/0.98  --res_ordering                          kbo
% 3.03/0.98  --res_to_prop_solver                    active
% 3.03/0.98  --res_prop_simpl_new                    false
% 3.03/0.98  --res_prop_simpl_given                  true
% 3.03/0.98  --res_passive_queue_type                priority_queues
% 3.03/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.98  --res_passive_queues_freq               [15;5]
% 3.03/0.98  --res_forward_subs                      full
% 3.03/0.98  --res_backward_subs                     full
% 3.03/0.98  --res_forward_subs_resolution           true
% 3.03/0.98  --res_backward_subs_resolution          true
% 3.03/0.98  --res_orphan_elimination                true
% 3.03/0.98  --res_time_limit                        2.
% 3.03/0.98  --res_out_proof                         true
% 3.03/0.98  
% 3.03/0.98  ------ Superposition Options
% 3.03/0.98  
% 3.03/0.98  --superposition_flag                    true
% 3.03/0.98  --sup_passive_queue_type                priority_queues
% 3.03/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.98  --demod_completeness_check              fast
% 3.03/0.98  --demod_use_ground                      true
% 3.03/0.98  --sup_to_prop_solver                    passive
% 3.03/0.98  --sup_prop_simpl_new                    true
% 3.03/0.98  --sup_prop_simpl_given                  true
% 3.03/0.98  --sup_fun_splitting                     false
% 3.03/0.98  --sup_smt_interval                      50000
% 3.03/0.98  
% 3.03/0.98  ------ Superposition Simplification Setup
% 3.03/0.98  
% 3.03/0.98  --sup_indices_passive                   []
% 3.03/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_full_bw                           [BwDemod]
% 3.03/0.98  --sup_immed_triv                        [TrivRules]
% 3.03/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_immed_bw_main                     []
% 3.03/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.98  
% 3.03/0.98  ------ Combination Options
% 3.03/0.98  
% 3.03/0.98  --comb_res_mult                         3
% 3.03/0.98  --comb_sup_mult                         2
% 3.03/0.98  --comb_inst_mult                        10
% 3.03/0.98  
% 3.03/0.98  ------ Debug Options
% 3.03/0.98  
% 3.03/0.98  --dbg_backtrace                         false
% 3.03/0.98  --dbg_dump_prop_clauses                 false
% 3.03/0.98  --dbg_dump_prop_clauses_file            -
% 3.03/0.98  --dbg_out_stat                          false
% 3.03/0.98  ------ Parsing...
% 3.03/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/0.98  ------ Proving...
% 3.03/0.98  ------ Problem Properties 
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  clauses                                 17
% 3.03/0.98  conjectures                             1
% 3.03/0.98  EPR                                     1
% 3.03/0.98  Horn                                    17
% 3.03/0.98  unary                                   7
% 3.03/0.98  binary                                  6
% 3.03/0.98  lits                                    33
% 3.03/0.98  lits eq                                 5
% 3.03/0.98  fd_pure                                 0
% 3.03/0.98  fd_pseudo                               0
% 3.03/0.98  fd_cond                                 0
% 3.03/0.98  fd_pseudo_cond                          0
% 3.03/0.98  AC symbols                              0
% 3.03/0.98  
% 3.03/0.98  ------ Schedule dynamic 5 is on 
% 3.03/0.98  
% 3.03/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  ------ 
% 3.03/0.98  Current options:
% 3.03/0.98  ------ 
% 3.03/0.98  
% 3.03/0.98  ------ Input Options
% 3.03/0.98  
% 3.03/0.98  --out_options                           all
% 3.03/0.98  --tptp_safe_out                         true
% 3.03/0.98  --problem_path                          ""
% 3.03/0.98  --include_path                          ""
% 3.03/0.98  --clausifier                            res/vclausify_rel
% 3.03/0.98  --clausifier_options                    --mode clausify
% 3.03/0.98  --stdin                                 false
% 3.03/0.98  --stats_out                             all
% 3.03/0.98  
% 3.03/0.98  ------ General Options
% 3.03/0.98  
% 3.03/0.98  --fof                                   false
% 3.03/0.98  --time_out_real                         305.
% 3.03/0.98  --time_out_virtual                      -1.
% 3.03/0.98  --symbol_type_check                     false
% 3.03/0.98  --clausify_out                          false
% 3.03/0.98  --sig_cnt_out                           false
% 3.03/0.98  --trig_cnt_out                          false
% 3.03/0.98  --trig_cnt_out_tolerance                1.
% 3.03/0.98  --trig_cnt_out_sk_spl                   false
% 3.03/0.98  --abstr_cl_out                          false
% 3.03/0.98  
% 3.03/0.98  ------ Global Options
% 3.03/0.98  
% 3.03/0.98  --schedule                              default
% 3.03/0.98  --add_important_lit                     false
% 3.03/0.98  --prop_solver_per_cl                    1000
% 3.03/0.98  --min_unsat_core                        false
% 3.03/0.98  --soft_assumptions                      false
% 3.03/0.98  --soft_lemma_size                       3
% 3.03/0.98  --prop_impl_unit_size                   0
% 3.03/0.98  --prop_impl_unit                        []
% 3.03/0.98  --share_sel_clauses                     true
% 3.03/0.98  --reset_solvers                         false
% 3.03/0.98  --bc_imp_inh                            [conj_cone]
% 3.03/0.98  --conj_cone_tolerance                   3.
% 3.03/0.98  --extra_neg_conj                        none
% 3.03/0.98  --large_theory_mode                     true
% 3.03/0.98  --prolific_symb_bound                   200
% 3.03/0.98  --lt_threshold                          2000
% 3.03/0.98  --clause_weak_htbl                      true
% 3.03/0.98  --gc_record_bc_elim                     false
% 3.03/0.98  
% 3.03/0.98  ------ Preprocessing Options
% 3.03/0.98  
% 3.03/0.98  --preprocessing_flag                    true
% 3.03/0.98  --time_out_prep_mult                    0.1
% 3.03/0.98  --splitting_mode                        input
% 3.03/0.98  --splitting_grd                         true
% 3.03/0.98  --splitting_cvd                         false
% 3.03/0.98  --splitting_cvd_svl                     false
% 3.03/0.98  --splitting_nvd                         32
% 3.03/0.98  --sub_typing                            true
% 3.03/0.98  --prep_gs_sim                           true
% 3.03/0.98  --prep_unflatten                        true
% 3.03/0.98  --prep_res_sim                          true
% 3.03/0.98  --prep_upred                            true
% 3.03/0.98  --prep_sem_filter                       exhaustive
% 3.03/0.98  --prep_sem_filter_out                   false
% 3.03/0.98  --pred_elim                             true
% 3.03/0.98  --res_sim_input                         true
% 3.03/0.98  --eq_ax_congr_red                       true
% 3.03/0.98  --pure_diseq_elim                       true
% 3.03/0.98  --brand_transform                       false
% 3.03/0.98  --non_eq_to_eq                          false
% 3.03/0.98  --prep_def_merge                        true
% 3.03/0.98  --prep_def_merge_prop_impl              false
% 3.03/0.98  --prep_def_merge_mbd                    true
% 3.03/0.98  --prep_def_merge_tr_red                 false
% 3.03/0.98  --prep_def_merge_tr_cl                  false
% 3.03/0.98  --smt_preprocessing                     true
% 3.03/0.98  --smt_ac_axioms                         fast
% 3.03/0.98  --preprocessed_out                      false
% 3.03/0.98  --preprocessed_stats                    false
% 3.03/0.98  
% 3.03/0.98  ------ Abstraction refinement Options
% 3.03/0.98  
% 3.03/0.98  --abstr_ref                             []
% 3.03/0.98  --abstr_ref_prep                        false
% 3.03/0.98  --abstr_ref_until_sat                   false
% 3.03/0.98  --abstr_ref_sig_restrict                funpre
% 3.03/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.98  --abstr_ref_under                       []
% 3.03/0.98  
% 3.03/0.98  ------ SAT Options
% 3.03/0.98  
% 3.03/0.98  --sat_mode                              false
% 3.03/0.98  --sat_fm_restart_options                ""
% 3.03/0.98  --sat_gr_def                            false
% 3.03/0.98  --sat_epr_types                         true
% 3.03/0.98  --sat_non_cyclic_types                  false
% 3.03/0.98  --sat_finite_models                     false
% 3.03/0.98  --sat_fm_lemmas                         false
% 3.03/0.98  --sat_fm_prep                           false
% 3.03/0.98  --sat_fm_uc_incr                        true
% 3.03/0.98  --sat_out_model                         small
% 3.03/0.98  --sat_out_clauses                       false
% 3.03/0.98  
% 3.03/0.98  ------ QBF Options
% 3.03/0.98  
% 3.03/0.98  --qbf_mode                              false
% 3.03/0.98  --qbf_elim_univ                         false
% 3.03/0.98  --qbf_dom_inst                          none
% 3.03/0.98  --qbf_dom_pre_inst                      false
% 3.03/0.98  --qbf_sk_in                             false
% 3.03/0.98  --qbf_pred_elim                         true
% 3.03/0.98  --qbf_split                             512
% 3.03/0.98  
% 3.03/0.98  ------ BMC1 Options
% 3.03/0.98  
% 3.03/0.98  --bmc1_incremental                      false
% 3.03/0.98  --bmc1_axioms                           reachable_all
% 3.03/0.98  --bmc1_min_bound                        0
% 3.03/0.98  --bmc1_max_bound                        -1
% 3.03/0.98  --bmc1_max_bound_default                -1
% 3.03/0.98  --bmc1_symbol_reachability              true
% 3.03/0.98  --bmc1_property_lemmas                  false
% 3.03/0.98  --bmc1_k_induction                      false
% 3.03/0.98  --bmc1_non_equiv_states                 false
% 3.03/0.98  --bmc1_deadlock                         false
% 3.03/0.98  --bmc1_ucm                              false
% 3.03/0.98  --bmc1_add_unsat_core                   none
% 3.03/0.98  --bmc1_unsat_core_children              false
% 3.03/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.98  --bmc1_out_stat                         full
% 3.03/0.98  --bmc1_ground_init                      false
% 3.03/0.98  --bmc1_pre_inst_next_state              false
% 3.03/0.98  --bmc1_pre_inst_state                   false
% 3.03/0.98  --bmc1_pre_inst_reach_state             false
% 3.03/0.98  --bmc1_out_unsat_core                   false
% 3.03/0.98  --bmc1_aig_witness_out                  false
% 3.03/0.98  --bmc1_verbose                          false
% 3.03/0.98  --bmc1_dump_clauses_tptp                false
% 3.03/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.98  --bmc1_dump_file                        -
% 3.03/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.98  --bmc1_ucm_extend_mode                  1
% 3.03/0.98  --bmc1_ucm_init_mode                    2
% 3.03/0.98  --bmc1_ucm_cone_mode                    none
% 3.03/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.98  --bmc1_ucm_relax_model                  4
% 3.03/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.98  --bmc1_ucm_layered_model                none
% 3.03/0.98  --bmc1_ucm_max_lemma_size               10
% 3.03/0.98  
% 3.03/0.98  ------ AIG Options
% 3.03/0.98  
% 3.03/0.98  --aig_mode                              false
% 3.03/0.98  
% 3.03/0.98  ------ Instantiation Options
% 3.03/0.98  
% 3.03/0.98  --instantiation_flag                    true
% 3.03/0.98  --inst_sos_flag                         false
% 3.03/0.98  --inst_sos_phase                        true
% 3.03/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.98  --inst_lit_sel_side                     none
% 3.03/0.98  --inst_solver_per_active                1400
% 3.03/0.98  --inst_solver_calls_frac                1.
% 3.03/0.98  --inst_passive_queue_type               priority_queues
% 3.03/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.98  --inst_passive_queues_freq              [25;2]
% 3.03/0.98  --inst_dismatching                      true
% 3.03/0.98  --inst_eager_unprocessed_to_passive     true
% 3.03/0.98  --inst_prop_sim_given                   true
% 3.03/0.98  --inst_prop_sim_new                     false
% 3.03/0.98  --inst_subs_new                         false
% 3.03/0.98  --inst_eq_res_simp                      false
% 3.03/0.98  --inst_subs_given                       false
% 3.03/0.98  --inst_orphan_elimination               true
% 3.03/0.98  --inst_learning_loop_flag               true
% 3.03/0.98  --inst_learning_start                   3000
% 3.03/0.98  --inst_learning_factor                  2
% 3.03/0.98  --inst_start_prop_sim_after_learn       3
% 3.03/0.98  --inst_sel_renew                        solver
% 3.03/0.98  --inst_lit_activity_flag                true
% 3.03/0.98  --inst_restr_to_given                   false
% 3.03/0.98  --inst_activity_threshold               500
% 3.03/0.98  --inst_out_proof                        true
% 3.03/0.98  
% 3.03/0.98  ------ Resolution Options
% 3.03/0.98  
% 3.03/0.98  --resolution_flag                       false
% 3.03/0.98  --res_lit_sel                           adaptive
% 3.03/0.98  --res_lit_sel_side                      none
% 3.03/0.98  --res_ordering                          kbo
% 3.03/0.98  --res_to_prop_solver                    active
% 3.03/0.98  --res_prop_simpl_new                    false
% 3.03/0.98  --res_prop_simpl_given                  true
% 3.03/0.98  --res_passive_queue_type                priority_queues
% 3.03/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.98  --res_passive_queues_freq               [15;5]
% 3.03/0.98  --res_forward_subs                      full
% 3.03/0.98  --res_backward_subs                     full
% 3.03/0.98  --res_forward_subs_resolution           true
% 3.03/0.98  --res_backward_subs_resolution          true
% 3.03/0.98  --res_orphan_elimination                true
% 3.03/0.98  --res_time_limit                        2.
% 3.03/0.98  --res_out_proof                         true
% 3.03/0.98  
% 3.03/0.98  ------ Superposition Options
% 3.03/0.98  
% 3.03/0.98  --superposition_flag                    true
% 3.03/0.98  --sup_passive_queue_type                priority_queues
% 3.03/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.98  --demod_completeness_check              fast
% 3.03/0.98  --demod_use_ground                      true
% 3.03/0.98  --sup_to_prop_solver                    passive
% 3.03/0.98  --sup_prop_simpl_new                    true
% 3.03/0.98  --sup_prop_simpl_given                  true
% 3.03/0.98  --sup_fun_splitting                     false
% 3.03/0.98  --sup_smt_interval                      50000
% 3.03/0.98  
% 3.03/0.98  ------ Superposition Simplification Setup
% 3.03/0.98  
% 3.03/0.98  --sup_indices_passive                   []
% 3.03/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_full_bw                           [BwDemod]
% 3.03/0.98  --sup_immed_triv                        [TrivRules]
% 3.03/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_immed_bw_main                     []
% 3.03/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.98  
% 3.03/0.98  ------ Combination Options
% 3.03/0.98  
% 3.03/0.98  --comb_res_mult                         3
% 3.03/0.98  --comb_sup_mult                         2
% 3.03/0.98  --comb_inst_mult                        10
% 3.03/0.98  
% 3.03/0.98  ------ Debug Options
% 3.03/0.98  
% 3.03/0.98  --dbg_backtrace                         false
% 3.03/0.98  --dbg_dump_prop_clauses                 false
% 3.03/0.98  --dbg_dump_prop_clauses_file            -
% 3.03/0.98  --dbg_out_stat                          false
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  ------ Proving...
% 3.03/0.98  
% 3.03/0.98  
% 3.03/0.98  % SZS status Theorem for theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/0.98  
% 3.03/0.98  fof(f14,conjecture,(
% 3.03/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f15,negated_conjecture,(
% 3.03/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 3.03/0.98    inference(negated_conjecture,[],[f14])).
% 3.03/0.98  
% 3.03/0.98  fof(f16,plain,(
% 3.03/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 3.03/0.98    inference(pure_predicate_removal,[],[f15])).
% 3.03/0.98  
% 3.03/0.98  fof(f31,plain,(
% 3.03/0.98    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.03/0.98    inference(ennf_transformation,[],[f16])).
% 3.03/0.98  
% 3.03/0.98  fof(f32,plain,(
% 3.03/0.98    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.03/0.98    inference(flattening,[],[f31])).
% 3.03/0.98  
% 3.03/0.98  fof(f39,plain,(
% 3.03/0.98    ( ! [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~m2_connsp_2(k2_struct_0(X0),X0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.03/0.98    introduced(choice_axiom,[])).
% 3.03/0.98  
% 3.03/0.98  fof(f38,plain,(
% 3.03/0.98    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK1),sK1,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.03/0.98    introduced(choice_axiom,[])).
% 3.03/0.98  
% 3.03/0.98  fof(f40,plain,(
% 3.03/0.98    (~m2_connsp_2(k2_struct_0(sK1),sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 3.03/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f32,f39,f38])).
% 3.03/0.98  
% 3.03/0.98  fof(f60,plain,(
% 3.03/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.03/0.98    inference(cnf_transformation,[],[f40])).
% 3.03/0.98  
% 3.03/0.98  fof(f6,axiom,(
% 3.03/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f33,plain,(
% 3.03/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.03/0.98    inference(nnf_transformation,[],[f6])).
% 3.03/0.98  
% 3.03/0.98  fof(f46,plain,(
% 3.03/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f33])).
% 3.03/0.98  
% 3.03/0.98  fof(f5,axiom,(
% 3.03/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f45,plain,(
% 3.03/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.03/0.98    inference(cnf_transformation,[],[f5])).
% 3.03/0.98  
% 3.03/0.98  fof(f4,axiom,(
% 3.03/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f44,plain,(
% 3.03/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.03/0.98    inference(cnf_transformation,[],[f4])).
% 3.03/0.98  
% 3.03/0.98  fof(f12,axiom,(
% 3.03/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f27,plain,(
% 3.03/0.98    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/0.98    inference(ennf_transformation,[],[f12])).
% 3.03/0.98  
% 3.03/0.98  fof(f28,plain,(
% 3.03/0.98    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/0.98    inference(flattening,[],[f27])).
% 3.03/0.98  
% 3.03/0.98  fof(f55,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f28])).
% 3.03/0.98  
% 3.03/0.98  fof(f59,plain,(
% 3.03/0.98    l1_pre_topc(sK1)),
% 3.03/0.98    inference(cnf_transformation,[],[f40])).
% 3.03/0.98  
% 3.03/0.98  fof(f47,plain,(
% 3.03/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f33])).
% 3.03/0.98  
% 3.03/0.98  fof(f10,axiom,(
% 3.03/0.98    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f24,plain,(
% 3.03/0.98    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/0.98    inference(ennf_transformation,[],[f10])).
% 3.03/0.98  
% 3.03/0.98  fof(f35,plain,(
% 3.03/0.98    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.03/0.98    introduced(choice_axiom,[])).
% 3.03/0.98  
% 3.03/0.98  fof(f36,plain,(
% 3.03/0.98    ! [X0] : ((v1_tops_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f35])).
% 3.03/0.98  
% 3.03/0.98  fof(f53,plain,(
% 3.03/0.98    ( ! [X0] : (v1_tops_1(sK0(X0),X0) | ~l1_pre_topc(X0)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f36])).
% 3.03/0.98  
% 3.03/0.98  fof(f52,plain,(
% 3.03/0.98    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f36])).
% 3.03/0.98  
% 3.03/0.98  fof(f9,axiom,(
% 3.03/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f23,plain,(
% 3.03/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/0.98    inference(ennf_transformation,[],[f9])).
% 3.03/0.98  
% 3.03/0.98  fof(f34,plain,(
% 3.03/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/0.98    inference(nnf_transformation,[],[f23])).
% 3.03/0.98  
% 3.03/0.98  fof(f50,plain,(
% 3.03/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f34])).
% 3.03/0.98  
% 3.03/0.98  fof(f8,axiom,(
% 3.03/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f22,plain,(
% 3.03/0.98    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.03/0.98    inference(ennf_transformation,[],[f8])).
% 3.03/0.98  
% 3.03/0.98  fof(f49,plain,(
% 3.03/0.98    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f22])).
% 3.03/0.98  
% 3.03/0.98  fof(f2,axiom,(
% 3.03/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f18,plain,(
% 3.03/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.03/0.98    inference(ennf_transformation,[],[f2])).
% 3.03/0.98  
% 3.03/0.98  fof(f19,plain,(
% 3.03/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.03/0.98    inference(flattening,[],[f18])).
% 3.03/0.98  
% 3.03/0.98  fof(f42,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f19])).
% 3.03/0.98  
% 3.03/0.98  fof(f7,axiom,(
% 3.03/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f20,plain,(
% 3.03/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.03/0.98    inference(ennf_transformation,[],[f7])).
% 3.03/0.98  
% 3.03/0.98  fof(f21,plain,(
% 3.03/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.03/0.98    inference(flattening,[],[f20])).
% 3.03/0.98  
% 3.03/0.98  fof(f48,plain,(
% 3.03/0.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f21])).
% 3.03/0.98  
% 3.03/0.98  fof(f61,plain,(
% 3.03/0.98    ~m2_connsp_2(k2_struct_0(sK1),sK1,sK2)),
% 3.03/0.98    inference(cnf_transformation,[],[f40])).
% 3.03/0.98  
% 3.03/0.98  fof(f13,axiom,(
% 3.03/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f29,plain,(
% 3.03/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/0.98    inference(ennf_transformation,[],[f13])).
% 3.03/0.98  
% 3.03/0.98  fof(f30,plain,(
% 3.03/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.98    inference(flattening,[],[f29])).
% 3.03/0.98  
% 3.03/0.98  fof(f37,plain,(
% 3.03/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.98    inference(nnf_transformation,[],[f30])).
% 3.03/0.98  
% 3.03/0.98  fof(f57,plain,(
% 3.03/0.98    ( ! [X2,X0,X1] : (m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f37])).
% 3.03/0.98  
% 3.03/0.98  fof(f58,plain,(
% 3.03/0.98    v2_pre_topc(sK1)),
% 3.03/0.98    inference(cnf_transformation,[],[f40])).
% 3.03/0.98  
% 3.03/0.98  fof(f11,axiom,(
% 3.03/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 3.03/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.03/0.98  
% 3.03/0.98  fof(f25,plain,(
% 3.03/0.98    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.03/0.98    inference(ennf_transformation,[],[f11])).
% 3.03/0.98  
% 3.03/0.98  fof(f26,plain,(
% 3.03/0.98    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.03/0.98    inference(flattening,[],[f25])).
% 3.03/0.98  
% 3.03/0.98  fof(f54,plain,(
% 3.03/0.98    ( ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.03/0.98    inference(cnf_transformation,[],[f26])).
% 3.03/0.98  
% 3.03/0.98  cnf(c_18,negated_conjecture,
% 3.03/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.03/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_995,plain,
% 3.03/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_6,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.03/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_996,plain,
% 3.03/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.03/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1854,plain,
% 3.03/0.98      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_995,c_996]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4,plain,
% 3.03/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.03/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_998,plain,
% 3.03/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_3,plain,
% 3.03/0.98      ( k2_subset_1(X0) = X0 ),
% 3.03/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1010,plain,
% 3.03/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.03/0.98      inference(light_normalisation,[status(thm)],[c_998,c_3]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_14,plain,
% 3.03/0.98      ( ~ v1_tops_1(X0,X1)
% 3.03/0.98      | v1_tops_1(X2,X1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | ~ r1_tarski(X0,X2)
% 3.03/0.98      | ~ l1_pre_topc(X1) ),
% 3.03/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_19,negated_conjecture,
% 3.03/0.98      ( l1_pre_topc(sK1) ),
% 3.03/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_368,plain,
% 3.03/0.98      ( ~ v1_tops_1(X0,X1)
% 3.03/0.98      | v1_tops_1(X2,X1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | ~ r1_tarski(X0,X2)
% 3.03/0.98      | sK1 != X1 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_369,plain,
% 3.03/0.98      ( ~ v1_tops_1(X0,sK1)
% 3.03/0.98      | v1_tops_1(X1,sK1)
% 3.03/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.98      | ~ r1_tarski(X0,X1) ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_368]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_991,plain,
% 3.03/0.98      ( v1_tops_1(X0,sK1) != iProver_top
% 3.03/0.98      | v1_tops_1(X1,sK1) = iProver_top
% 3.03/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.03/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.03/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1583,plain,
% 3.03/0.98      ( v1_tops_1(X0,sK1) != iProver_top
% 3.03/0.98      | v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top
% 3.03/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.03/0.98      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_1010,c_991]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_5,plain,
% 3.03/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.03/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1144,plain,
% 3.03/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.98      | ~ r1_tarski(X0,u1_struct_0(sK1)) ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1145,plain,
% 3.03/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.03/0.98      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_1144]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4049,plain,
% 3.03/0.98      ( v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top
% 3.03/0.98      | v1_tops_1(X0,sK1) != iProver_top
% 3.03/0.98      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_1583,c_1145]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4050,plain,
% 3.03/0.98      ( v1_tops_1(X0,sK1) != iProver_top
% 3.03/0.98      | v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top
% 3.03/0.98      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 3.03/0.98      inference(renaming,[status(thm)],[c_4049]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4058,plain,
% 3.03/0.98      ( v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top
% 3.03/0.98      | v1_tops_1(sK2,sK1) != iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_1854,c_4050]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_22,plain,
% 3.03/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_11,plain,
% 3.03/0.98      ( v1_tops_1(sK0(X0),X0) | ~ l1_pre_topc(X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_38,plain,
% 3.03/0.98      ( v1_tops_1(sK0(X0),X0) = iProver_top
% 3.03/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_40,plain,
% 3.03/0.98      ( v1_tops_1(sK0(sK1),sK1) = iProver_top
% 3.03/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_38]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_12,plain,
% 3.03/0.98      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.03/0.98      | ~ l1_pre_topc(X0) ),
% 3.03/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_354,plain,
% 3.03/0.98      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK1 != X0 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_355,plain,
% 3.03/0.98      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_354]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_993,plain,
% 3.03/0.98      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1855,plain,
% 3.03/0.98      ( r1_tarski(sK0(sK1),u1_struct_0(sK1)) = iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_993,c_996]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4059,plain,
% 3.03/0.98      ( v1_tops_1(sK0(sK1),sK1) != iProver_top
% 3.03/0.98      | v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_1855,c_4050]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4299,plain,
% 3.03/0.98      ( v1_tops_1(u1_struct_0(sK1),sK1) = iProver_top ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_4058,c_22,c_40,c_4059]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_10,plain,
% 3.03/0.98      ( ~ v1_tops_1(X0,X1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | ~ l1_pre_topc(X1)
% 3.03/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.03/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_387,plain,
% 3.03/0.98      ( ~ v1_tops_1(X0,X1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 3.03/0.98      | sK1 != X1 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_388,plain,
% 3.03/0.98      ( ~ v1_tops_1(X0,sK1)
% 3.03/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.98      | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_387]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_990,plain,
% 3.03/0.98      ( k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
% 3.03/0.98      | v1_tops_1(X0,sK1) != iProver_top
% 3.03/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1498,plain,
% 3.03/0.98      ( k2_pre_topc(sK1,u1_struct_0(sK1)) = k2_struct_0(sK1)
% 3.03/0.98      | v1_tops_1(u1_struct_0(sK1),sK1) != iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_1010,c_990]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4306,plain,
% 3.03/0.98      ( k2_pre_topc(sK1,u1_struct_0(sK1)) = k2_struct_0(sK1) ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_4299,c_1498]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_8,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.03/0.98      | ~ l1_pre_topc(X1) ),
% 3.03/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_417,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.03/0.98      | sK1 != X1 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_418,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.98      | r1_tarski(X0,k2_pre_topc(sK1,X0)) ),
% 3.03/0.98      inference(unflattening,[status(thm)],[c_417]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_988,plain,
% 3.03/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.03/0.98      | r1_tarski(X0,k2_pre_topc(sK1,X0)) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1418,plain,
% 3.03/0.98      ( r1_tarski(u1_struct_0(sK1),k2_pre_topc(sK1,u1_struct_0(sK1))) = iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_1010,c_988]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_4889,plain,
% 3.03/0.98      ( r1_tarski(u1_struct_0(sK1),k2_struct_0(sK1)) = iProver_top ),
% 3.03/0.98      inference(demodulation,[status(thm)],[c_4306,c_1418]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1,plain,
% 3.03/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.03/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1000,plain,
% 3.03/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.03/0.98      | r1_tarski(X1,X2) != iProver_top
% 3.03/0.98      | r1_tarski(X0,X2) = iProver_top ),
% 3.03/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_2175,plain,
% 3.03/0.98      ( r1_tarski(u1_struct_0(sK1),X0) != iProver_top
% 3.03/0.98      | r1_tarski(sK2,X0) = iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_1854,c_1000]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_5073,plain,
% 3.03/0.98      ( r1_tarski(sK2,k2_struct_0(sK1)) = iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_4889,c_2175]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1496,plain,
% 3.03/0.98      ( k2_pre_topc(sK1,sK0(sK1)) = k2_struct_0(sK1)
% 3.03/0.98      | v1_tops_1(sK0(sK1),sK1) != iProver_top ),
% 3.03/0.98      inference(superposition,[status(thm)],[c_993,c_990]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_36,plain,
% 3.03/0.98      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.98      | ~ l1_pre_topc(sK1) ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_39,plain,
% 3.03/0.98      ( v1_tops_1(sK0(sK1),sK1) | ~ l1_pre_topc(sK1) ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1111,plain,
% 3.03/0.98      ( ~ v1_tops_1(sK0(sK1),sK1)
% 3.03/0.98      | ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.98      | k2_pre_topc(sK1,sK0(sK1)) = k2_struct_0(sK1) ),
% 3.03/0.98      inference(instantiation,[status(thm)],[c_388]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_1839,plain,
% 3.03/0.98      ( k2_pre_topc(sK1,sK0(sK1)) = k2_struct_0(sK1) ),
% 3.03/0.98      inference(global_propositional_subsumption,
% 3.03/0.98                [status(thm)],
% 3.03/0.98                [c_1496,c_19,c_36,c_39,c_1111]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_7,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | ~ l1_pre_topc(X1) ),
% 3.03/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_429,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.98      | sK1 != X1 ),
% 3.03/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 3.03/0.98  
% 3.03/0.98  cnf(c_430,plain,
% 3.03/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.98      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_987,plain,
% 3.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.03/0.99      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1845,plain,
% 3.03/0.99      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.03/0.99      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.03/0.99      inference(superposition,[status(thm)],[c_1839,c_987]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_17,negated_conjecture,
% 3.03/0.99      ( ~ m2_connsp_2(k2_struct_0(sK1),sK1,sK2) ),
% 3.03/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_15,plain,
% 3.03/0.99      ( m2_connsp_2(X0,X1,X2)
% 3.03/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.99      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 3.03/0.99      | ~ v2_pre_topc(X1)
% 3.03/0.99      | ~ l1_pre_topc(X1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_20,negated_conjecture,
% 3.03/0.99      ( v2_pre_topc(sK1) ),
% 3.03/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_301,plain,
% 3.03/0.99      ( m2_connsp_2(X0,X1,X2)
% 3.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.03/0.99      | ~ r1_tarski(X2,k1_tops_1(X1,X0))
% 3.03/0.99      | ~ l1_pre_topc(X1)
% 3.03/0.99      | sK1 != X1 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_302,plain,
% 3.03/0.99      ( m2_connsp_2(X0,sK1,X1)
% 3.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 3.03/0.99      | ~ l1_pre_topc(sK1) ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_306,plain,
% 3.03/0.99      ( ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 3.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | m2_connsp_2(X0,sK1,X1) ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_302,c_19]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_307,plain,
% 3.03/0.99      ( m2_connsp_2(X0,sK1,X1)
% 3.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | ~ r1_tarski(X1,k1_tops_1(sK1,X0)) ),
% 3.03/0.99      inference(renaming,[status(thm)],[c_306]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_337,plain,
% 3.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | ~ r1_tarski(X1,k1_tops_1(sK1,X0))
% 3.03/0.99      | k2_struct_0(sK1) != X0
% 3.03/0.99      | sK2 != X1
% 3.03/0.99      | sK1 != sK1 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_307]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_338,plain,
% 3.03/0.99      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_337]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_340,plain,
% 3.03/0.99      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.03/0.99      | ~ r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_338,c_18]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_994,plain,
% 3.03/0.99      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.03/0.99      | r1_tarski(sK2,k1_tops_1(sK1,k2_struct_0(sK1))) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_13,plain,
% 3.03/0.99      ( ~ v2_pre_topc(X0)
% 3.03/0.99      | ~ l1_pre_topc(X0)
% 3.03/0.99      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 3.03/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_269,plain,
% 3.03/0.99      ( ~ l1_pre_topc(X0)
% 3.03/0.99      | k1_tops_1(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 3.03/0.99      | sK1 != X0 ),
% 3.03/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_270,plain,
% 3.03/0.99      ( ~ l1_pre_topc(sK1)
% 3.03/0.99      | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 3.03/0.99      inference(unflattening,[status(thm)],[c_269]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_33,plain,
% 3.03/0.99      ( ~ v2_pre_topc(sK1)
% 3.03/0.99      | ~ l1_pre_topc(sK1)
% 3.03/0.99      | k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_272,plain,
% 3.03/0.99      ( k1_tops_1(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 3.03/0.99      inference(global_propositional_subsumption,
% 3.03/0.99                [status(thm)],
% 3.03/0.99                [c_270,c_20,c_19,c_33]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_1037,plain,
% 3.03/0.99      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.03/0.99      | r1_tarski(sK2,k2_struct_0(sK1)) != iProver_top ),
% 3.03/0.99      inference(light_normalisation,[status(thm)],[c_994,c_272]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_35,plain,
% 3.03/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.03/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.03/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(c_37,plain,
% 3.03/0.99      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.03/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.03/0.99      inference(instantiation,[status(thm)],[c_35]) ).
% 3.03/0.99  
% 3.03/0.99  cnf(contradiction,plain,
% 3.03/0.99      ( $false ),
% 3.03/0.99      inference(minisat,[status(thm)],[c_5073,c_1845,c_1037,c_37,c_22]) ).
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  ------                               Statistics
% 3.03/0.99  
% 3.03/0.99  ------ General
% 3.03/0.99  
% 3.03/0.99  abstr_ref_over_cycles:                  0
% 3.03/0.99  abstr_ref_under_cycles:                 0
% 3.03/0.99  gc_basic_clause_elim:                   0
% 3.03/0.99  forced_gc_time:                         0
% 3.03/0.99  parsing_time:                           0.008
% 3.03/0.99  unif_index_cands_time:                  0.
% 3.03/0.99  unif_index_add_time:                    0.
% 3.03/0.99  orderings_time:                         0.
% 3.03/0.99  out_proof_time:                         0.007
% 3.03/0.99  total_time:                             0.186
% 3.03/0.99  num_of_symbols:                         47
% 3.03/0.99  num_of_terms:                           3700
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing
% 3.03/0.99  
% 3.03/0.99  num_of_splits:                          0
% 3.03/0.99  num_of_split_atoms:                     0
% 3.03/0.99  num_of_reused_defs:                     0
% 3.03/0.99  num_eq_ax_congr_red:                    17
% 3.03/0.99  num_of_sem_filtered_clauses:            1
% 3.03/0.99  num_of_subtypes:                        0
% 3.03/0.99  monotx_restored_types:                  0
% 3.03/0.99  sat_num_of_epr_types:                   0
% 3.03/0.99  sat_num_of_non_cyclic_types:            0
% 3.03/0.99  sat_guarded_non_collapsed_types:        0
% 3.03/0.99  num_pure_diseq_elim:                    0
% 3.03/0.99  simp_replaced_by:                       0
% 3.03/0.99  res_preprocessed:                       95
% 3.03/0.99  prep_upred:                             0
% 3.03/0.99  prep_unflattend:                        12
% 3.03/0.99  smt_new_axioms:                         0
% 3.03/0.99  pred_elim_cands:                        3
% 3.03/0.99  pred_elim:                              3
% 3.03/0.99  pred_elim_cl:                           4
% 3.03/0.99  pred_elim_cycles:                       5
% 3.03/0.99  merged_defs:                            8
% 3.03/0.99  merged_defs_ncl:                        0
% 3.03/0.99  bin_hyper_res:                          8
% 3.03/0.99  prep_cycles:                            4
% 3.03/0.99  pred_elim_time:                         0.004
% 3.03/0.99  splitting_time:                         0.
% 3.03/0.99  sem_filter_time:                        0.
% 3.03/0.99  monotx_time:                            0.
% 3.03/0.99  subtype_inf_time:                       0.
% 3.03/0.99  
% 3.03/0.99  ------ Problem properties
% 3.03/0.99  
% 3.03/0.99  clauses:                                17
% 3.03/0.99  conjectures:                            1
% 3.03/0.99  epr:                                    1
% 3.03/0.99  horn:                                   17
% 3.03/0.99  ground:                                 5
% 3.03/0.99  unary:                                  7
% 3.03/0.99  binary:                                 6
% 3.03/0.99  lits:                                   33
% 3.03/0.99  lits_eq:                                5
% 3.03/0.99  fd_pure:                                0
% 3.03/0.99  fd_pseudo:                              0
% 3.03/0.99  fd_cond:                                0
% 3.03/0.99  fd_pseudo_cond:                         0
% 3.03/0.99  ac_symbols:                             0
% 3.03/0.99  
% 3.03/0.99  ------ Propositional Solver
% 3.03/0.99  
% 3.03/0.99  prop_solver_calls:                      28
% 3.03/0.99  prop_fast_solver_calls:                 628
% 3.03/0.99  smt_solver_calls:                       0
% 3.03/0.99  smt_fast_solver_calls:                  0
% 3.03/0.99  prop_num_of_clauses:                    2172
% 3.03/0.99  prop_preprocess_simplified:             5667
% 3.03/0.99  prop_fo_subsumed:                       18
% 3.03/0.99  prop_solver_time:                       0.
% 3.03/0.99  smt_solver_time:                        0.
% 3.03/0.99  smt_fast_solver_time:                   0.
% 3.03/0.99  prop_fast_solver_time:                  0.
% 3.03/0.99  prop_unsat_core_time:                   0.
% 3.03/0.99  
% 3.03/0.99  ------ QBF
% 3.03/0.99  
% 3.03/0.99  qbf_q_res:                              0
% 3.03/0.99  qbf_num_tautologies:                    0
% 3.03/0.99  qbf_prep_cycles:                        0
% 3.03/0.99  
% 3.03/0.99  ------ BMC1
% 3.03/0.99  
% 3.03/0.99  bmc1_current_bound:                     -1
% 3.03/0.99  bmc1_last_solved_bound:                 -1
% 3.03/0.99  bmc1_unsat_core_size:                   -1
% 3.03/0.99  bmc1_unsat_core_parents_size:           -1
% 3.03/0.99  bmc1_merge_next_fun:                    0
% 3.03/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.03/0.99  
% 3.03/0.99  ------ Instantiation
% 3.03/0.99  
% 3.03/0.99  inst_num_of_clauses:                    747
% 3.03/0.99  inst_num_in_passive:                    191
% 3.03/0.99  inst_num_in_active:                     314
% 3.03/0.99  inst_num_in_unprocessed:                242
% 3.03/0.99  inst_num_of_loops:                      330
% 3.03/0.99  inst_num_of_learning_restarts:          0
% 3.03/0.99  inst_num_moves_active_passive:          13
% 3.03/0.99  inst_lit_activity:                      0
% 3.03/0.99  inst_lit_activity_moves:                0
% 3.03/0.99  inst_num_tautologies:                   0
% 3.03/0.99  inst_num_prop_implied:                  0
% 3.03/0.99  inst_num_existing_simplified:           0
% 3.03/0.99  inst_num_eq_res_simplified:             0
% 3.03/0.99  inst_num_child_elim:                    0
% 3.03/0.99  inst_num_of_dismatching_blockings:      104
% 3.03/0.99  inst_num_of_non_proper_insts:           691
% 3.03/0.99  inst_num_of_duplicates:                 0
% 3.03/0.99  inst_inst_num_from_inst_to_res:         0
% 3.03/0.99  inst_dismatching_checking_time:         0.
% 3.03/0.99  
% 3.03/0.99  ------ Resolution
% 3.03/0.99  
% 3.03/0.99  res_num_of_clauses:                     0
% 3.03/0.99  res_num_in_passive:                     0
% 3.03/0.99  res_num_in_active:                      0
% 3.03/0.99  res_num_of_loops:                       99
% 3.03/0.99  res_forward_subset_subsumed:            20
% 3.03/0.99  res_backward_subset_subsumed:           0
% 3.03/0.99  res_forward_subsumed:                   0
% 3.03/0.99  res_backward_subsumed:                  0
% 3.03/0.99  res_forward_subsumption_resolution:     0
% 3.03/0.99  res_backward_subsumption_resolution:    0
% 3.03/0.99  res_clause_to_clause_subsumption:       339
% 3.03/0.99  res_orphan_elimination:                 0
% 3.03/0.99  res_tautology_del:                      70
% 3.03/0.99  res_num_eq_res_simplified:              0
% 3.03/0.99  res_num_sel_changes:                    0
% 3.03/0.99  res_moves_from_active_to_pass:          0
% 3.03/0.99  
% 3.03/0.99  ------ Superposition
% 3.03/0.99  
% 3.03/0.99  sup_time_total:                         0.
% 3.03/0.99  sup_time_generating:                    0.
% 3.03/0.99  sup_time_sim_full:                      0.
% 3.03/0.99  sup_time_sim_immed:                     0.
% 3.03/0.99  
% 3.03/0.99  sup_num_of_clauses:                     91
% 3.03/0.99  sup_num_in_active:                      59
% 3.03/0.99  sup_num_in_passive:                     32
% 3.03/0.99  sup_num_of_loops:                       65
% 3.03/0.99  sup_fw_superposition:                   75
% 3.03/0.99  sup_bw_superposition:                   82
% 3.03/0.99  sup_immediate_simplified:               30
% 3.03/0.99  sup_given_eliminated:                   0
% 3.03/0.99  comparisons_done:                       0
% 3.03/0.99  comparisons_avoided:                    0
% 3.03/0.99  
% 3.03/0.99  ------ Simplifications
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  sim_fw_subset_subsumed:                 16
% 3.03/0.99  sim_bw_subset_subsumed:                 3
% 3.03/0.99  sim_fw_subsumed:                        10
% 3.03/0.99  sim_bw_subsumed:                        0
% 3.03/0.99  sim_fw_subsumption_res:                 0
% 3.03/0.99  sim_bw_subsumption_res:                 0
% 3.03/0.99  sim_tautology_del:                      7
% 3.03/0.99  sim_eq_tautology_del:                   1
% 3.03/0.99  sim_eq_res_simp:                        0
% 3.03/0.99  sim_fw_demodulated:                     0
% 3.03/0.99  sim_bw_demodulated:                     5
% 3.03/0.99  sim_light_normalised:                   12
% 3.03/0.99  sim_joinable_taut:                      0
% 3.03/0.99  sim_joinable_simp:                      0
% 3.03/0.99  sim_ac_normalised:                      0
% 3.03/0.99  sim_smt_subsumption:                    0
% 3.03/0.99  
%------------------------------------------------------------------------------
