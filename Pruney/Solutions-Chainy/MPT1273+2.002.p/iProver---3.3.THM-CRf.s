%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:21 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 273 expanded)
%              Number of clauses        :   61 (  98 expanded)
%              Number of leaves         :   11 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  304 ( 928 expanded)
%              Number of equality atoms :   65 (  92 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v2_tops_1(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_1(X1,X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_1(X1,X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tops_1(X1,X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tops_1(sK1,X0)
        & v3_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tops_1(X1,X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tops_1(X1,sK0)
          & v3_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ v2_tops_1(sK1,sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f26,f25])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_1(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_410,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_588,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
    | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_586,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_41))) = k1_tops_1(sK0,X0_41) ),
    inference(subtyping,[status(esa)],[c_260])).

cnf(c_591,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_41))) = k1_tops_1(sK0,X0_41)
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_873,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_41)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0_41))
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_591])).

cnf(c_2024,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_588,c_873])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
    | k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_587,plain,
    ( k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_896,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_588,c_587])).

cnf(c_2047,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_2024,c_896])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_tops_1(X0,X2)
    | v1_tops_1(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_283,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_tops_1(X0,X2)
    | v1_tops_1(X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_284,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_tops_1(X0,sK0)
    | v1_tops_1(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_8,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_247,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_248,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_317,plain,
    ( ~ v1_tops_1(X0,sK0)
    | v1_tops_1(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | X2 != X1
    | k1_tops_1(sK0,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_284,c_248])).

cnf(c_318,plain,
    ( v1_tops_1(X0,sK0)
    | ~ v1_tops_1(k1_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_405,plain,
    ( v1_tops_1(X0_41,sK0)
    | ~ v1_tops_1(k1_tops_1(sK0,X0_41),sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_318])).

cnf(c_593,plain,
    ( v1_tops_1(X0_41,sK0) = iProver_top
    | v1_tops_1(k1_tops_1(sK0,X0_41),sK0) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_2167,plain,
    ( v1_tops_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2047,c_593])).

cnf(c_2168,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2167,c_2047])).

cnf(c_649,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_41)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_650,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_41)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_652,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_646,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_647,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_272])).

cnf(c_438,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_440,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_5,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(k2_pre_topc(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,negated_conjecture,
    ( v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_194,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_11])).

cnf(c_195,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_194])).

cnf(c_197,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_195,c_13,c_12])).

cnf(c_219,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(sK0,sK1) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_197])).

cnf(c_220,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_222,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_220,c_13])).

cnf(c_223,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_224,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_4,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_208,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_209,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_210,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2168,c_652,c_647,c_440,c_224,c_210,c_15,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.81/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.81/0.99  
% 2.81/0.99  ------  iProver source info
% 2.81/0.99  
% 2.81/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.81/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.81/0.99  git: non_committed_changes: false
% 2.81/0.99  git: last_make_outside_of_git: false
% 2.81/0.99  
% 2.81/0.99  ------ 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options
% 2.81/0.99  
% 2.81/0.99  --out_options                           all
% 2.81/0.99  --tptp_safe_out                         true
% 2.81/0.99  --problem_path                          ""
% 2.81/0.99  --include_path                          ""
% 2.81/0.99  --clausifier                            res/vclausify_rel
% 2.81/0.99  --clausifier_options                    --mode clausify
% 2.81/0.99  --stdin                                 false
% 2.81/0.99  --stats_out                             all
% 2.81/0.99  
% 2.81/0.99  ------ General Options
% 2.81/0.99  
% 2.81/0.99  --fof                                   false
% 2.81/0.99  --time_out_real                         305.
% 2.81/0.99  --time_out_virtual                      -1.
% 2.81/0.99  --symbol_type_check                     false
% 2.81/0.99  --clausify_out                          false
% 2.81/0.99  --sig_cnt_out                           false
% 2.81/0.99  --trig_cnt_out                          false
% 2.81/0.99  --trig_cnt_out_tolerance                1.
% 2.81/0.99  --trig_cnt_out_sk_spl                   false
% 2.81/0.99  --abstr_cl_out                          false
% 2.81/0.99  
% 2.81/0.99  ------ Global Options
% 2.81/0.99  
% 2.81/0.99  --schedule                              default
% 2.81/0.99  --add_important_lit                     false
% 2.81/0.99  --prop_solver_per_cl                    1000
% 2.81/0.99  --min_unsat_core                        false
% 2.81/0.99  --soft_assumptions                      false
% 2.81/0.99  --soft_lemma_size                       3
% 2.81/0.99  --prop_impl_unit_size                   0
% 2.81/0.99  --prop_impl_unit                        []
% 2.81/0.99  --share_sel_clauses                     true
% 2.81/0.99  --reset_solvers                         false
% 2.81/0.99  --bc_imp_inh                            [conj_cone]
% 2.81/0.99  --conj_cone_tolerance                   3.
% 2.81/0.99  --extra_neg_conj                        none
% 2.81/0.99  --large_theory_mode                     true
% 2.81/0.99  --prolific_symb_bound                   200
% 2.81/0.99  --lt_threshold                          2000
% 2.81/0.99  --clause_weak_htbl                      true
% 2.81/0.99  --gc_record_bc_elim                     false
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing Options
% 2.81/0.99  
% 2.81/0.99  --preprocessing_flag                    true
% 2.81/0.99  --time_out_prep_mult                    0.1
% 2.81/0.99  --splitting_mode                        input
% 2.81/0.99  --splitting_grd                         true
% 2.81/0.99  --splitting_cvd                         false
% 2.81/0.99  --splitting_cvd_svl                     false
% 2.81/0.99  --splitting_nvd                         32
% 2.81/0.99  --sub_typing                            true
% 2.81/0.99  --prep_gs_sim                           true
% 2.81/0.99  --prep_unflatten                        true
% 2.81/0.99  --prep_res_sim                          true
% 2.81/0.99  --prep_upred                            true
% 2.81/0.99  --prep_sem_filter                       exhaustive
% 2.81/0.99  --prep_sem_filter_out                   false
% 2.81/0.99  --pred_elim                             true
% 2.81/0.99  --res_sim_input                         true
% 2.81/0.99  --eq_ax_congr_red                       true
% 2.81/0.99  --pure_diseq_elim                       true
% 2.81/0.99  --brand_transform                       false
% 2.81/0.99  --non_eq_to_eq                          false
% 2.81/0.99  --prep_def_merge                        true
% 2.81/0.99  --prep_def_merge_prop_impl              false
% 2.81/0.99  --prep_def_merge_mbd                    true
% 2.81/0.99  --prep_def_merge_tr_red                 false
% 2.81/0.99  --prep_def_merge_tr_cl                  false
% 2.81/0.99  --smt_preprocessing                     true
% 2.81/0.99  --smt_ac_axioms                         fast
% 2.81/0.99  --preprocessed_out                      false
% 2.81/0.99  --preprocessed_stats                    false
% 2.81/0.99  
% 2.81/0.99  ------ Abstraction refinement Options
% 2.81/0.99  
% 2.81/0.99  --abstr_ref                             []
% 2.81/0.99  --abstr_ref_prep                        false
% 2.81/0.99  --abstr_ref_until_sat                   false
% 2.81/0.99  --abstr_ref_sig_restrict                funpre
% 2.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/0.99  --abstr_ref_under                       []
% 2.81/0.99  
% 2.81/0.99  ------ SAT Options
% 2.81/0.99  
% 2.81/0.99  --sat_mode                              false
% 2.81/0.99  --sat_fm_restart_options                ""
% 2.81/0.99  --sat_gr_def                            false
% 2.81/0.99  --sat_epr_types                         true
% 2.81/0.99  --sat_non_cyclic_types                  false
% 2.81/0.99  --sat_finite_models                     false
% 2.81/0.99  --sat_fm_lemmas                         false
% 2.81/0.99  --sat_fm_prep                           false
% 2.81/0.99  --sat_fm_uc_incr                        true
% 2.81/0.99  --sat_out_model                         small
% 2.81/0.99  --sat_out_clauses                       false
% 2.81/0.99  
% 2.81/0.99  ------ QBF Options
% 2.81/0.99  
% 2.81/0.99  --qbf_mode                              false
% 2.81/0.99  --qbf_elim_univ                         false
% 2.81/0.99  --qbf_dom_inst                          none
% 2.81/0.99  --qbf_dom_pre_inst                      false
% 2.81/0.99  --qbf_sk_in                             false
% 2.81/0.99  --qbf_pred_elim                         true
% 2.81/0.99  --qbf_split                             512
% 2.81/0.99  
% 2.81/0.99  ------ BMC1 Options
% 2.81/0.99  
% 2.81/0.99  --bmc1_incremental                      false
% 2.81/0.99  --bmc1_axioms                           reachable_all
% 2.81/0.99  --bmc1_min_bound                        0
% 2.81/0.99  --bmc1_max_bound                        -1
% 2.81/0.99  --bmc1_max_bound_default                -1
% 2.81/0.99  --bmc1_symbol_reachability              true
% 2.81/0.99  --bmc1_property_lemmas                  false
% 2.81/0.99  --bmc1_k_induction                      false
% 2.81/0.99  --bmc1_non_equiv_states                 false
% 2.81/0.99  --bmc1_deadlock                         false
% 2.81/0.99  --bmc1_ucm                              false
% 2.81/0.99  --bmc1_add_unsat_core                   none
% 2.81/0.99  --bmc1_unsat_core_children              false
% 2.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/0.99  --bmc1_out_stat                         full
% 2.81/0.99  --bmc1_ground_init                      false
% 2.81/0.99  --bmc1_pre_inst_next_state              false
% 2.81/0.99  --bmc1_pre_inst_state                   false
% 2.81/0.99  --bmc1_pre_inst_reach_state             false
% 2.81/0.99  --bmc1_out_unsat_core                   false
% 2.81/0.99  --bmc1_aig_witness_out                  false
% 2.81/0.99  --bmc1_verbose                          false
% 2.81/0.99  --bmc1_dump_clauses_tptp                false
% 2.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.81/0.99  --bmc1_dump_file                        -
% 2.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.81/0.99  --bmc1_ucm_extend_mode                  1
% 2.81/0.99  --bmc1_ucm_init_mode                    2
% 2.81/0.99  --bmc1_ucm_cone_mode                    none
% 2.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.81/0.99  --bmc1_ucm_relax_model                  4
% 2.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/0.99  --bmc1_ucm_layered_model                none
% 2.81/0.99  --bmc1_ucm_max_lemma_size               10
% 2.81/0.99  
% 2.81/0.99  ------ AIG Options
% 2.81/0.99  
% 2.81/0.99  --aig_mode                              false
% 2.81/0.99  
% 2.81/0.99  ------ Instantiation Options
% 2.81/0.99  
% 2.81/0.99  --instantiation_flag                    true
% 2.81/0.99  --inst_sos_flag                         false
% 2.81/0.99  --inst_sos_phase                        true
% 2.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel_side                     num_symb
% 2.81/0.99  --inst_solver_per_active                1400
% 2.81/0.99  --inst_solver_calls_frac                1.
% 2.81/0.99  --inst_passive_queue_type               priority_queues
% 2.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/0.99  --inst_passive_queues_freq              [25;2]
% 2.81/0.99  --inst_dismatching                      true
% 2.81/0.99  --inst_eager_unprocessed_to_passive     true
% 2.81/0.99  --inst_prop_sim_given                   true
% 2.81/0.99  --inst_prop_sim_new                     false
% 2.81/0.99  --inst_subs_new                         false
% 2.81/0.99  --inst_eq_res_simp                      false
% 2.81/0.99  --inst_subs_given                       false
% 2.81/0.99  --inst_orphan_elimination               true
% 2.81/0.99  --inst_learning_loop_flag               true
% 2.81/0.99  --inst_learning_start                   3000
% 2.81/0.99  --inst_learning_factor                  2
% 2.81/0.99  --inst_start_prop_sim_after_learn       3
% 2.81/0.99  --inst_sel_renew                        solver
% 2.81/0.99  --inst_lit_activity_flag                true
% 2.81/0.99  --inst_restr_to_given                   false
% 2.81/0.99  --inst_activity_threshold               500
% 2.81/0.99  --inst_out_proof                        true
% 2.81/0.99  
% 2.81/0.99  ------ Resolution Options
% 2.81/0.99  
% 2.81/0.99  --resolution_flag                       true
% 2.81/0.99  --res_lit_sel                           adaptive
% 2.81/0.99  --res_lit_sel_side                      none
% 2.81/0.99  --res_ordering                          kbo
% 2.81/0.99  --res_to_prop_solver                    active
% 2.81/0.99  --res_prop_simpl_new                    false
% 2.81/0.99  --res_prop_simpl_given                  true
% 2.81/0.99  --res_passive_queue_type                priority_queues
% 2.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/0.99  --res_passive_queues_freq               [15;5]
% 2.81/0.99  --res_forward_subs                      full
% 2.81/0.99  --res_backward_subs                     full
% 2.81/0.99  --res_forward_subs_resolution           true
% 2.81/0.99  --res_backward_subs_resolution          true
% 2.81/0.99  --res_orphan_elimination                true
% 2.81/0.99  --res_time_limit                        2.
% 2.81/0.99  --res_out_proof                         true
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Options
% 2.81/0.99  
% 2.81/0.99  --superposition_flag                    true
% 2.81/0.99  --sup_passive_queue_type                priority_queues
% 2.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.81/0.99  --demod_completeness_check              fast
% 2.81/0.99  --demod_use_ground                      true
% 2.81/0.99  --sup_to_prop_solver                    passive
% 2.81/0.99  --sup_prop_simpl_new                    true
% 2.81/0.99  --sup_prop_simpl_given                  true
% 2.81/0.99  --sup_fun_splitting                     false
% 2.81/0.99  --sup_smt_interval                      50000
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Simplification Setup
% 2.81/0.99  
% 2.81/0.99  --sup_indices_passive                   []
% 2.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_full_bw                           [BwDemod]
% 2.81/0.99  --sup_immed_triv                        [TrivRules]
% 2.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_immed_bw_main                     []
% 2.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  
% 2.81/0.99  ------ Combination Options
% 2.81/0.99  
% 2.81/0.99  --comb_res_mult                         3
% 2.81/0.99  --comb_sup_mult                         2
% 2.81/0.99  --comb_inst_mult                        10
% 2.81/0.99  
% 2.81/0.99  ------ Debug Options
% 2.81/0.99  
% 2.81/0.99  --dbg_backtrace                         false
% 2.81/0.99  --dbg_dump_prop_clauses                 false
% 2.81/0.99  --dbg_dump_prop_clauses_file            -
% 2.81/0.99  --dbg_out_stat                          false
% 2.81/0.99  ------ Parsing...
% 2.81/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.81/0.99  ------ Proving...
% 2.81/0.99  ------ Problem Properties 
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  clauses                                 9
% 2.81/0.99  conjectures                             1
% 2.81/0.99  EPR                                     0
% 2.81/0.99  Horn                                    9
% 2.81/0.99  unary                                   3
% 2.81/0.99  binary                                  5
% 2.81/0.99  lits                                    17
% 2.81/0.99  lits eq                                 3
% 2.81/0.99  fd_pure                                 0
% 2.81/0.99  fd_pseudo                               0
% 2.81/0.99  fd_cond                                 0
% 2.81/0.99  fd_pseudo_cond                          0
% 2.81/0.99  AC symbols                              0
% 2.81/0.99  
% 2.81/0.99  ------ Schedule dynamic 5 is on 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  ------ 
% 2.81/0.99  Current options:
% 2.81/0.99  ------ 
% 2.81/0.99  
% 2.81/0.99  ------ Input Options
% 2.81/0.99  
% 2.81/0.99  --out_options                           all
% 2.81/0.99  --tptp_safe_out                         true
% 2.81/0.99  --problem_path                          ""
% 2.81/0.99  --include_path                          ""
% 2.81/0.99  --clausifier                            res/vclausify_rel
% 2.81/0.99  --clausifier_options                    --mode clausify
% 2.81/0.99  --stdin                                 false
% 2.81/0.99  --stats_out                             all
% 2.81/0.99  
% 2.81/0.99  ------ General Options
% 2.81/0.99  
% 2.81/0.99  --fof                                   false
% 2.81/0.99  --time_out_real                         305.
% 2.81/0.99  --time_out_virtual                      -1.
% 2.81/0.99  --symbol_type_check                     false
% 2.81/0.99  --clausify_out                          false
% 2.81/0.99  --sig_cnt_out                           false
% 2.81/0.99  --trig_cnt_out                          false
% 2.81/0.99  --trig_cnt_out_tolerance                1.
% 2.81/0.99  --trig_cnt_out_sk_spl                   false
% 2.81/0.99  --abstr_cl_out                          false
% 2.81/0.99  
% 2.81/0.99  ------ Global Options
% 2.81/0.99  
% 2.81/0.99  --schedule                              default
% 2.81/0.99  --add_important_lit                     false
% 2.81/0.99  --prop_solver_per_cl                    1000
% 2.81/0.99  --min_unsat_core                        false
% 2.81/0.99  --soft_assumptions                      false
% 2.81/0.99  --soft_lemma_size                       3
% 2.81/0.99  --prop_impl_unit_size                   0
% 2.81/0.99  --prop_impl_unit                        []
% 2.81/0.99  --share_sel_clauses                     true
% 2.81/0.99  --reset_solvers                         false
% 2.81/0.99  --bc_imp_inh                            [conj_cone]
% 2.81/0.99  --conj_cone_tolerance                   3.
% 2.81/0.99  --extra_neg_conj                        none
% 2.81/0.99  --large_theory_mode                     true
% 2.81/0.99  --prolific_symb_bound                   200
% 2.81/0.99  --lt_threshold                          2000
% 2.81/0.99  --clause_weak_htbl                      true
% 2.81/0.99  --gc_record_bc_elim                     false
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing Options
% 2.81/0.99  
% 2.81/0.99  --preprocessing_flag                    true
% 2.81/0.99  --time_out_prep_mult                    0.1
% 2.81/0.99  --splitting_mode                        input
% 2.81/0.99  --splitting_grd                         true
% 2.81/0.99  --splitting_cvd                         false
% 2.81/0.99  --splitting_cvd_svl                     false
% 2.81/0.99  --splitting_nvd                         32
% 2.81/0.99  --sub_typing                            true
% 2.81/0.99  --prep_gs_sim                           true
% 2.81/0.99  --prep_unflatten                        true
% 2.81/0.99  --prep_res_sim                          true
% 2.81/0.99  --prep_upred                            true
% 2.81/0.99  --prep_sem_filter                       exhaustive
% 2.81/0.99  --prep_sem_filter_out                   false
% 2.81/0.99  --pred_elim                             true
% 2.81/0.99  --res_sim_input                         true
% 2.81/0.99  --eq_ax_congr_red                       true
% 2.81/0.99  --pure_diseq_elim                       true
% 2.81/0.99  --brand_transform                       false
% 2.81/0.99  --non_eq_to_eq                          false
% 2.81/0.99  --prep_def_merge                        true
% 2.81/0.99  --prep_def_merge_prop_impl              false
% 2.81/0.99  --prep_def_merge_mbd                    true
% 2.81/0.99  --prep_def_merge_tr_red                 false
% 2.81/0.99  --prep_def_merge_tr_cl                  false
% 2.81/0.99  --smt_preprocessing                     true
% 2.81/0.99  --smt_ac_axioms                         fast
% 2.81/0.99  --preprocessed_out                      false
% 2.81/0.99  --preprocessed_stats                    false
% 2.81/0.99  
% 2.81/0.99  ------ Abstraction refinement Options
% 2.81/0.99  
% 2.81/0.99  --abstr_ref                             []
% 2.81/0.99  --abstr_ref_prep                        false
% 2.81/0.99  --abstr_ref_until_sat                   false
% 2.81/0.99  --abstr_ref_sig_restrict                funpre
% 2.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/0.99  --abstr_ref_under                       []
% 2.81/0.99  
% 2.81/0.99  ------ SAT Options
% 2.81/0.99  
% 2.81/0.99  --sat_mode                              false
% 2.81/0.99  --sat_fm_restart_options                ""
% 2.81/0.99  --sat_gr_def                            false
% 2.81/0.99  --sat_epr_types                         true
% 2.81/0.99  --sat_non_cyclic_types                  false
% 2.81/0.99  --sat_finite_models                     false
% 2.81/0.99  --sat_fm_lemmas                         false
% 2.81/0.99  --sat_fm_prep                           false
% 2.81/0.99  --sat_fm_uc_incr                        true
% 2.81/0.99  --sat_out_model                         small
% 2.81/0.99  --sat_out_clauses                       false
% 2.81/0.99  
% 2.81/0.99  ------ QBF Options
% 2.81/0.99  
% 2.81/0.99  --qbf_mode                              false
% 2.81/0.99  --qbf_elim_univ                         false
% 2.81/0.99  --qbf_dom_inst                          none
% 2.81/0.99  --qbf_dom_pre_inst                      false
% 2.81/0.99  --qbf_sk_in                             false
% 2.81/0.99  --qbf_pred_elim                         true
% 2.81/0.99  --qbf_split                             512
% 2.81/0.99  
% 2.81/0.99  ------ BMC1 Options
% 2.81/0.99  
% 2.81/0.99  --bmc1_incremental                      false
% 2.81/0.99  --bmc1_axioms                           reachable_all
% 2.81/0.99  --bmc1_min_bound                        0
% 2.81/0.99  --bmc1_max_bound                        -1
% 2.81/0.99  --bmc1_max_bound_default                -1
% 2.81/0.99  --bmc1_symbol_reachability              true
% 2.81/0.99  --bmc1_property_lemmas                  false
% 2.81/0.99  --bmc1_k_induction                      false
% 2.81/0.99  --bmc1_non_equiv_states                 false
% 2.81/0.99  --bmc1_deadlock                         false
% 2.81/0.99  --bmc1_ucm                              false
% 2.81/0.99  --bmc1_add_unsat_core                   none
% 2.81/0.99  --bmc1_unsat_core_children              false
% 2.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/0.99  --bmc1_out_stat                         full
% 2.81/0.99  --bmc1_ground_init                      false
% 2.81/0.99  --bmc1_pre_inst_next_state              false
% 2.81/0.99  --bmc1_pre_inst_state                   false
% 2.81/0.99  --bmc1_pre_inst_reach_state             false
% 2.81/0.99  --bmc1_out_unsat_core                   false
% 2.81/0.99  --bmc1_aig_witness_out                  false
% 2.81/0.99  --bmc1_verbose                          false
% 2.81/0.99  --bmc1_dump_clauses_tptp                false
% 2.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.81/0.99  --bmc1_dump_file                        -
% 2.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.81/0.99  --bmc1_ucm_extend_mode                  1
% 2.81/0.99  --bmc1_ucm_init_mode                    2
% 2.81/0.99  --bmc1_ucm_cone_mode                    none
% 2.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.81/0.99  --bmc1_ucm_relax_model                  4
% 2.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/0.99  --bmc1_ucm_layered_model                none
% 2.81/0.99  --bmc1_ucm_max_lemma_size               10
% 2.81/0.99  
% 2.81/0.99  ------ AIG Options
% 2.81/0.99  
% 2.81/0.99  --aig_mode                              false
% 2.81/0.99  
% 2.81/0.99  ------ Instantiation Options
% 2.81/0.99  
% 2.81/0.99  --instantiation_flag                    true
% 2.81/0.99  --inst_sos_flag                         false
% 2.81/0.99  --inst_sos_phase                        true
% 2.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/0.99  --inst_lit_sel_side                     none
% 2.81/0.99  --inst_solver_per_active                1400
% 2.81/0.99  --inst_solver_calls_frac                1.
% 2.81/0.99  --inst_passive_queue_type               priority_queues
% 2.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/0.99  --inst_passive_queues_freq              [25;2]
% 2.81/0.99  --inst_dismatching                      true
% 2.81/0.99  --inst_eager_unprocessed_to_passive     true
% 2.81/0.99  --inst_prop_sim_given                   true
% 2.81/0.99  --inst_prop_sim_new                     false
% 2.81/0.99  --inst_subs_new                         false
% 2.81/0.99  --inst_eq_res_simp                      false
% 2.81/0.99  --inst_subs_given                       false
% 2.81/0.99  --inst_orphan_elimination               true
% 2.81/0.99  --inst_learning_loop_flag               true
% 2.81/0.99  --inst_learning_start                   3000
% 2.81/0.99  --inst_learning_factor                  2
% 2.81/0.99  --inst_start_prop_sim_after_learn       3
% 2.81/0.99  --inst_sel_renew                        solver
% 2.81/0.99  --inst_lit_activity_flag                true
% 2.81/0.99  --inst_restr_to_given                   false
% 2.81/0.99  --inst_activity_threshold               500
% 2.81/0.99  --inst_out_proof                        true
% 2.81/0.99  
% 2.81/0.99  ------ Resolution Options
% 2.81/0.99  
% 2.81/0.99  --resolution_flag                       false
% 2.81/0.99  --res_lit_sel                           adaptive
% 2.81/0.99  --res_lit_sel_side                      none
% 2.81/0.99  --res_ordering                          kbo
% 2.81/0.99  --res_to_prop_solver                    active
% 2.81/0.99  --res_prop_simpl_new                    false
% 2.81/0.99  --res_prop_simpl_given                  true
% 2.81/0.99  --res_passive_queue_type                priority_queues
% 2.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/0.99  --res_passive_queues_freq               [15;5]
% 2.81/0.99  --res_forward_subs                      full
% 2.81/0.99  --res_backward_subs                     full
% 2.81/0.99  --res_forward_subs_resolution           true
% 2.81/0.99  --res_backward_subs_resolution          true
% 2.81/0.99  --res_orphan_elimination                true
% 2.81/0.99  --res_time_limit                        2.
% 2.81/0.99  --res_out_proof                         true
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Options
% 2.81/0.99  
% 2.81/0.99  --superposition_flag                    true
% 2.81/0.99  --sup_passive_queue_type                priority_queues
% 2.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.81/0.99  --demod_completeness_check              fast
% 2.81/0.99  --demod_use_ground                      true
% 2.81/0.99  --sup_to_prop_solver                    passive
% 2.81/0.99  --sup_prop_simpl_new                    true
% 2.81/0.99  --sup_prop_simpl_given                  true
% 2.81/0.99  --sup_fun_splitting                     false
% 2.81/0.99  --sup_smt_interval                      50000
% 2.81/0.99  
% 2.81/0.99  ------ Superposition Simplification Setup
% 2.81/0.99  
% 2.81/0.99  --sup_indices_passive                   []
% 2.81/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_full_bw                           [BwDemod]
% 2.81/0.99  --sup_immed_triv                        [TrivRules]
% 2.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_immed_bw_main                     []
% 2.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/0.99  
% 2.81/0.99  ------ Combination Options
% 2.81/0.99  
% 2.81/0.99  --comb_res_mult                         3
% 2.81/0.99  --comb_sup_mult                         2
% 2.81/0.99  --comb_inst_mult                        10
% 2.81/0.99  
% 2.81/0.99  ------ Debug Options
% 2.81/0.99  
% 2.81/0.99  --dbg_backtrace                         false
% 2.81/0.99  --dbg_dump_prop_clauses                 false
% 2.81/0.99  --dbg_dump_prop_clauses_file            -
% 2.81/0.99  --dbg_out_stat                          false
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  ------ Proving...
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  % SZS status Theorem for theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  fof(f9,conjecture,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f10,negated_conjecture,(
% 2.81/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 2.81/0.99    inference(negated_conjecture,[],[f9])).
% 2.81/0.99  
% 2.81/0.99  fof(f21,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : ((~v2_tops_1(X1,X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f10])).
% 2.81/0.99  
% 2.81/0.99  fof(f22,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : (~v2_tops_1(X1,X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.81/0.99    inference(flattening,[],[f21])).
% 2.81/0.99  
% 2.81/0.99  fof(f26,plain,(
% 2.81/0.99    ( ! [X0] : (? [X1] : (~v2_tops_1(X1,X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tops_1(sK1,X0) & v3_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f25,plain,(
% 2.81/0.99    ? [X0] : (? [X1] : (~v2_tops_1(X1,X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~v2_tops_1(X1,sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.81/0.99    introduced(choice_axiom,[])).
% 2.81/0.99  
% 2.81/0.99  fof(f27,plain,(
% 2.81/0.99    (~v2_tops_1(sK1,sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f26,f25])).
% 2.81/0.99  
% 2.81/0.99  fof(f39,plain,(
% 2.81/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.81/0.99    inference(cnf_transformation,[],[f27])).
% 2.81/0.99  
% 2.81/0.99  fof(f1,axiom,(
% 2.81/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f11,plain,(
% 2.81/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f1])).
% 2.81/0.99  
% 2.81/0.99  fof(f28,plain,(
% 2.81/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.81/0.99    inference(cnf_transformation,[],[f11])).
% 2.81/0.99  
% 2.81/0.99  fof(f4,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f15,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f4])).
% 2.81/0.99  
% 2.81/0.99  fof(f31,plain,(
% 2.81/0.99    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f15])).
% 2.81/0.99  
% 2.81/0.99  fof(f38,plain,(
% 2.81/0.99    l1_pre_topc(sK0)),
% 2.81/0.99    inference(cnf_transformation,[],[f27])).
% 2.81/0.99  
% 2.81/0.99  fof(f2,axiom,(
% 2.81/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f12,plain,(
% 2.81/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f2])).
% 2.81/0.99  
% 2.81/0.99  fof(f29,plain,(
% 2.81/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.81/0.99    inference(cnf_transformation,[],[f12])).
% 2.81/0.99  
% 2.81/0.99  fof(f8,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f19,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f8])).
% 2.81/0.99  
% 2.81/0.99  fof(f20,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(flattening,[],[f19])).
% 2.81/0.99  
% 2.81/0.99  fof(f37,plain,(
% 2.81/0.99    ( ! [X2,X0,X1] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f20])).
% 2.81/0.99  
% 2.81/0.99  fof(f7,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f18,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f7])).
% 2.81/0.99  
% 2.81/0.99  fof(f36,plain,(
% 2.81/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f18])).
% 2.81/0.99  
% 2.81/0.99  fof(f3,axiom,(
% 2.81/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f13,plain,(
% 2.81/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.81/0.99    inference(ennf_transformation,[],[f3])).
% 2.81/0.99  
% 2.81/0.99  fof(f14,plain,(
% 2.81/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(flattening,[],[f13])).
% 2.81/0.99  
% 2.81/0.99  fof(f30,plain,(
% 2.81/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f14])).
% 2.81/0.99  
% 2.81/0.99  fof(f5,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f16,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f5])).
% 2.81/0.99  
% 2.81/0.99  fof(f23,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(nnf_transformation,[],[f16])).
% 2.81/0.99  
% 2.81/0.99  fof(f32,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f23])).
% 2.81/0.99  
% 2.81/0.99  fof(f6,axiom,(
% 2.81/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 2.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.81/0.99  
% 2.81/0.99  fof(f17,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(ennf_transformation,[],[f6])).
% 2.81/0.99  
% 2.81/0.99  fof(f24,plain,(
% 2.81/0.99    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.99    inference(nnf_transformation,[],[f17])).
% 2.81/0.99  
% 2.81/0.99  fof(f34,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f24])).
% 2.81/0.99  
% 2.81/0.99  fof(f40,plain,(
% 2.81/0.99    v3_tops_1(sK1,sK0)),
% 2.81/0.99    inference(cnf_transformation,[],[f27])).
% 2.81/0.99  
% 2.81/0.99  fof(f33,plain,(
% 2.81/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.81/0.99    inference(cnf_transformation,[],[f23])).
% 2.81/0.99  
% 2.81/0.99  fof(f41,plain,(
% 2.81/0.99    ~v2_tops_1(sK1,sK0)),
% 2.81/0.99    inference(cnf_transformation,[],[f27])).
% 2.81/0.99  
% 2.81/0.99  cnf(c_12,negated_conjecture,
% 2.81/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_410,negated_conjecture,
% 2.81/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_588,plain,
% 2.81/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_0,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.81/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.81/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_412,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
% 2.81/0.99      | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_586,plain,
% 2.81/0.99      ( m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top
% 2.81/0.99      | m1_subset_1(k3_subset_1(X0_44,X0_41),k1_zfmisc_1(X0_44)) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_3,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ l1_pre_topc(X1)
% 2.81/0.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_13,negated_conjecture,
% 2.81/0.99      ( l1_pre_topc(sK0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_259,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 2.81/0.99      | sK0 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_260,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_259]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_407,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_41))) = k1_tops_1(sK0,X0_41) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_260]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_591,plain,
% 2.81/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_41))) = k1_tops_1(sK0,X0_41)
% 2.81/0.99      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_873,plain,
% 2.81/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0_41)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0_41))
% 2.81/0.99      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_586,c_591]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2024,plain,
% 2.81/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_588,c_873]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_1,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.81/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.81/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_411,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_44))
% 2.81/0.99      | k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41 ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_587,plain,
% 2.81/0.99      ( k3_subset_1(X0_44,k3_subset_1(X0_44,X0_41)) = X0_41
% 2.81/0.99      | m1_subset_1(X0_41,k1_zfmisc_1(X0_44)) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_896,plain,
% 2.81/0.99      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_588,c_587]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2047,plain,
% 2.81/0.99      ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 2.81/0.99      inference(light_normalisation,[status(thm)],[c_2024,c_896]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_9,plain,
% 2.81/0.99      ( ~ r1_tarski(X0,X1)
% 2.81/0.99      | ~ v1_tops_1(X0,X2)
% 2.81/0.99      | v1_tops_1(X1,X2)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.81/0.99      | ~ l1_pre_topc(X2) ),
% 2.81/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_283,plain,
% 2.81/0.99      ( ~ r1_tarski(X0,X1)
% 2.81/0.99      | ~ v1_tops_1(X0,X2)
% 2.81/0.99      | v1_tops_1(X1,X2)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.81/0.99      | sK0 != X2 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_284,plain,
% 2.81/0.99      ( ~ r1_tarski(X0,X1)
% 2.81/0.99      | ~ v1_tops_1(X0,sK0)
% 2.81/0.99      | v1_tops_1(X1,sK0)
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_283]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_8,plain,
% 2.81/0.99      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_247,plain,
% 2.81/0.99      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | sK0 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_248,plain,
% 2.81/0.99      ( r1_tarski(k1_tops_1(sK0,X0),X0)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_247]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_317,plain,
% 2.81/0.99      ( ~ v1_tops_1(X0,sK0)
% 2.81/0.99      | v1_tops_1(X1,sK0)
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | X2 != X1
% 2.81/0.99      | k1_tops_1(sK0,X2) != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_284,c_248]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_318,plain,
% 2.81/0.99      ( v1_tops_1(X0,sK0)
% 2.81/0.99      | ~ v1_tops_1(k1_tops_1(sK0,X0),sK0)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_317]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_405,plain,
% 2.81/0.99      ( v1_tops_1(X0_41,sK0)
% 2.81/0.99      | ~ v1_tops_1(k1_tops_1(sK0,X0_41),sK0)
% 2.81/0.99      | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | ~ m1_subset_1(k1_tops_1(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_318]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_593,plain,
% 2.81/0.99      ( v1_tops_1(X0_41,sK0) = iProver_top
% 2.81/0.99      | v1_tops_1(k1_tops_1(sK0,X0_41),sK0) != iProver_top
% 2.81/0.99      | m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.81/0.99      | m1_subset_1(k1_tops_1(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2167,plain,
% 2.81/0.99      ( v1_tops_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0) != iProver_top
% 2.81/0.99      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top
% 2.81/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.81/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.81/0.99      inference(superposition,[status(thm)],[c_2047,c_593]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2168,plain,
% 2.81/0.99      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) != iProver_top
% 2.81/0.99      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top
% 2.81/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.81/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.81/0.99      inference(light_normalisation,[status(thm)],[c_2167,c_2047]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_649,plain,
% 2.81/0.99      ( ~ m1_subset_1(k2_pre_topc(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_41)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_412]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_650,plain,
% 2.81/0.99      ( m1_subset_1(k2_pre_topc(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.81/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_41)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_652,plain,
% 2.81/0.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.81/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_650]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_646,plain,
% 2.81/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_412]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_647,plain,
% 2.81/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.81/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_2,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_271,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | sK0 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_272,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_271]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_406,plain,
% 2.81/0.99      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | m1_subset_1(k2_pre_topc(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(subtyping,[status(esa)],[c_272]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_438,plain,
% 2.81/0.99      ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.81/0.99      | m1_subset_1(k2_pre_topc(sK0,X0_41),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_440,plain,
% 2.81/0.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.81/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.81/0.99      inference(instantiation,[status(thm)],[c_438]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_5,plain,
% 2.81/0.99      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.81/0.99      | ~ v2_tops_1(X1,X0)
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_7,plain,
% 2.81/0.99      ( ~ v3_tops_1(X0,X1)
% 2.81/0.99      | v2_tops_1(k2_pre_topc(X1,X0),X1)
% 2.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.81/0.99      | ~ l1_pre_topc(X1) ),
% 2.81/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_11,negated_conjecture,
% 2.81/0.99      ( v3_tops_1(sK1,sK0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_194,plain,
% 2.81/0.99      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | sK0 != X0
% 2.81/0.99      | sK1 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_11]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_195,plain,
% 2.81/0.99      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 2.81/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | ~ l1_pre_topc(sK0) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_194]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_197,plain,
% 2.81/0.99      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_195,c_13,c_12]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_219,plain,
% 2.81/0.99      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | k2_pre_topc(sK0,sK1) != X1
% 2.81/0.99      | sK0 != X0 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_197]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_220,plain,
% 2.81/0.99      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
% 2.81/0.99      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | ~ l1_pre_topc(sK0) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_219]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_222,plain,
% 2.81/0.99      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
% 2.81/0.99      inference(global_propositional_subsumption,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_220,c_13]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_223,plain,
% 2.81/0.99      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
% 2.81/0.99      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.81/0.99      inference(renaming,[status(thm)],[c_222]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_224,plain,
% 2.81/0.99      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) = iProver_top
% 2.81/0.99      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_4,plain,
% 2.81/0.99      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.81/0.99      | v2_tops_1(X1,X0)
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | ~ l1_pre_topc(X0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_10,negated_conjecture,
% 2.81/0.99      ( ~ v2_tops_1(sK1,sK0) ),
% 2.81/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_208,plain,
% 2.81/0.99      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 2.81/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.81/0.99      | ~ l1_pre_topc(X0)
% 2.81/0.99      | sK0 != X0
% 2.81/0.99      | sK1 != X1 ),
% 2.81/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_10]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_209,plain,
% 2.81/0.99      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 2.81/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.81/0.99      | ~ l1_pre_topc(sK0) ),
% 2.81/0.99      inference(unflattening,[status(thm)],[c_208]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_210,plain,
% 2.81/0.99      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) != iProver_top
% 2.81/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.81/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_15,plain,
% 2.81/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(c_14,plain,
% 2.81/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 2.81/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.81/0.99  
% 2.81/0.99  cnf(contradiction,plain,
% 2.81/0.99      ( $false ),
% 2.81/0.99      inference(minisat,
% 2.81/0.99                [status(thm)],
% 2.81/0.99                [c_2168,c_652,c_647,c_440,c_224,c_210,c_15,c_14]) ).
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.81/0.99  
% 2.81/0.99  ------                               Statistics
% 2.81/0.99  
% 2.81/0.99  ------ General
% 2.81/0.99  
% 2.81/0.99  abstr_ref_over_cycles:                  0
% 2.81/0.99  abstr_ref_under_cycles:                 0
% 2.81/0.99  gc_basic_clause_elim:                   0
% 2.81/0.99  forced_gc_time:                         0
% 2.81/0.99  parsing_time:                           0.009
% 2.81/0.99  unif_index_cands_time:                  0.
% 2.81/0.99  unif_index_add_time:                    0.
% 2.81/0.99  orderings_time:                         0.
% 2.81/0.99  out_proof_time:                         0.01
% 2.81/0.99  total_time:                             0.104
% 2.81/0.99  num_of_symbols:                         45
% 2.81/0.99  num_of_terms:                           1565
% 2.81/0.99  
% 2.81/0.99  ------ Preprocessing
% 2.81/0.99  
% 2.81/0.99  num_of_splits:                          0
% 2.81/0.99  num_of_split_atoms:                     0
% 2.81/0.99  num_of_reused_defs:                     0
% 2.81/0.99  num_eq_ax_congr_red:                    14
% 2.81/0.99  num_of_sem_filtered_clauses:            1
% 2.81/0.99  num_of_subtypes:                        4
% 2.81/0.99  monotx_restored_types:                  0
% 2.81/0.99  sat_num_of_epr_types:                   0
% 2.81/0.99  sat_num_of_non_cyclic_types:            0
% 2.81/0.99  sat_guarded_non_collapsed_types:        1
% 2.81/0.99  num_pure_diseq_elim:                    0
% 2.81/0.99  simp_replaced_by:                       0
% 2.81/0.99  res_preprocessed:                       54
% 2.81/0.99  prep_upred:                             0
% 2.81/0.99  prep_unflattend:                        14
% 2.81/0.99  smt_new_axioms:                         0
% 2.81/0.99  pred_elim_cands:                        2
% 2.81/0.99  pred_elim:                              4
% 2.81/0.99  pred_elim_cl:                           5
% 2.81/0.99  pred_elim_cycles:                       7
% 2.81/0.99  merged_defs:                            0
% 2.81/0.99  merged_defs_ncl:                        0
% 2.81/0.99  bin_hyper_res:                          0
% 2.81/0.99  prep_cycles:                            4
% 2.81/0.99  pred_elim_time:                         0.003
% 2.81/0.99  splitting_time:                         0.
% 2.81/0.99  sem_filter_time:                        0.
% 2.81/0.99  monotx_time:                            0.
% 2.81/0.99  subtype_inf_time:                       0.
% 2.81/0.99  
% 2.81/0.99  ------ Problem properties
% 2.81/0.99  
% 2.81/0.99  clauses:                                9
% 2.81/0.99  conjectures:                            1
% 2.81/0.99  epr:                                    0
% 2.81/0.99  horn:                                   9
% 2.81/0.99  ground:                                 4
% 2.81/0.99  unary:                                  3
% 2.81/0.99  binary:                                 5
% 2.81/0.99  lits:                                   17
% 2.81/0.99  lits_eq:                                3
% 2.81/0.99  fd_pure:                                0
% 2.81/0.99  fd_pseudo:                              0
% 2.81/0.99  fd_cond:                                0
% 2.81/0.99  fd_pseudo_cond:                         0
% 2.81/0.99  ac_symbols:                             0
% 2.81/0.99  
% 2.81/0.99  ------ Propositional Solver
% 2.81/0.99  
% 2.81/0.99  prop_solver_calls:                      28
% 2.81/0.99  prop_fast_solver_calls:                 330
% 2.81/0.99  smt_solver_calls:                       0
% 2.81/0.99  smt_fast_solver_calls:                  0
% 2.81/0.99  prop_num_of_clauses:                    597
% 2.81/0.99  prop_preprocess_simplified:             2208
% 2.81/0.99  prop_fo_subsumed:                       10
% 2.81/0.99  prop_solver_time:                       0.
% 2.81/0.99  smt_solver_time:                        0.
% 2.81/0.99  smt_fast_solver_time:                   0.
% 2.81/0.99  prop_fast_solver_time:                  0.
% 2.81/0.99  prop_unsat_core_time:                   0.
% 2.81/0.99  
% 2.81/0.99  ------ QBF
% 2.81/0.99  
% 2.81/0.99  qbf_q_res:                              0
% 2.81/0.99  qbf_num_tautologies:                    0
% 2.81/0.99  qbf_prep_cycles:                        0
% 2.81/0.99  
% 2.81/0.99  ------ BMC1
% 2.81/0.99  
% 2.81/0.99  bmc1_current_bound:                     -1
% 2.81/0.99  bmc1_last_solved_bound:                 -1
% 2.81/0.99  bmc1_unsat_core_size:                   -1
% 2.81/0.99  bmc1_unsat_core_parents_size:           -1
% 2.81/0.99  bmc1_merge_next_fun:                    0
% 2.81/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.81/0.99  
% 2.81/0.99  ------ Instantiation
% 2.81/0.99  
% 2.81/0.99  inst_num_of_clauses:                    252
% 2.81/0.99  inst_num_in_passive:                    79
% 2.81/0.99  inst_num_in_active:                     148
% 2.81/0.99  inst_num_in_unprocessed:                25
% 2.81/0.99  inst_num_of_loops:                      160
% 2.81/0.99  inst_num_of_learning_restarts:          0
% 2.81/0.99  inst_num_moves_active_passive:          7
% 2.81/0.99  inst_lit_activity:                      0
% 2.81/0.99  inst_lit_activity_moves:                0
% 2.81/0.99  inst_num_tautologies:                   0
% 2.81/0.99  inst_num_prop_implied:                  0
% 2.81/0.99  inst_num_existing_simplified:           0
% 2.81/0.99  inst_num_eq_res_simplified:             0
% 2.81/0.99  inst_num_child_elim:                    0
% 2.81/0.99  inst_num_of_dismatching_blockings:      111
% 2.81/0.99  inst_num_of_non_proper_insts:           330
% 2.81/0.99  inst_num_of_duplicates:                 0
% 2.81/0.99  inst_inst_num_from_inst_to_res:         0
% 2.81/0.99  inst_dismatching_checking_time:         0.
% 2.81/0.99  
% 2.81/0.99  ------ Resolution
% 2.81/0.99  
% 2.81/0.99  res_num_of_clauses:                     0
% 2.81/0.99  res_num_in_passive:                     0
% 2.81/0.99  res_num_in_active:                      0
% 2.81/0.99  res_num_of_loops:                       58
% 2.81/0.99  res_forward_subset_subsumed:            75
% 2.81/0.99  res_backward_subset_subsumed:           0
% 2.81/0.99  res_forward_subsumed:                   0
% 2.81/0.99  res_backward_subsumed:                  0
% 2.81/0.99  res_forward_subsumption_resolution:     0
% 2.81/0.99  res_backward_subsumption_resolution:    0
% 2.81/0.99  res_clause_to_clause_subsumption:       124
% 2.81/0.99  res_orphan_elimination:                 0
% 2.81/0.99  res_tautology_del:                      72
% 2.81/0.99  res_num_eq_res_simplified:              1
% 2.81/0.99  res_num_sel_changes:                    0
% 2.81/0.99  res_moves_from_active_to_pass:          0
% 2.81/0.99  
% 2.81/0.99  ------ Superposition
% 2.81/0.99  
% 2.81/0.99  sup_time_total:                         0.
% 2.81/0.99  sup_time_generating:                    0.
% 2.81/0.99  sup_time_sim_full:                      0.
% 2.81/0.99  sup_time_sim_immed:                     0.
% 2.81/0.99  
% 2.81/0.99  sup_num_of_clauses:                     58
% 2.81/0.99  sup_num_in_active:                      29
% 2.81/0.99  sup_num_in_passive:                     29
% 2.81/0.99  sup_num_of_loops:                       30
% 2.81/0.99  sup_fw_superposition:                   40
% 2.81/0.99  sup_bw_superposition:                   28
% 2.81/0.99  sup_immediate_simplified:               18
% 2.81/0.99  sup_given_eliminated:                   0
% 2.81/0.99  comparisons_done:                       0
% 2.81/0.99  comparisons_avoided:                    0
% 2.81/0.99  
% 2.81/0.99  ------ Simplifications
% 2.81/0.99  
% 2.81/0.99  
% 2.81/0.99  sim_fw_subset_subsumed:                 2
% 2.81/0.99  sim_bw_subset_subsumed:                 2
% 2.81/0.99  sim_fw_subsumed:                        0
% 2.81/0.99  sim_bw_subsumed:                        0
% 2.81/0.99  sim_fw_subsumption_res:                 0
% 2.81/0.99  sim_bw_subsumption_res:                 0
% 2.81/0.99  sim_tautology_del:                      0
% 2.81/0.99  sim_eq_tautology_del:                   12
% 2.81/0.99  sim_eq_res_simp:                        0
% 2.81/0.99  sim_fw_demodulated:                     0
% 2.81/0.99  sim_bw_demodulated:                     0
% 2.81/0.99  sim_light_normalised:                   16
% 2.81/0.99  sim_joinable_taut:                      0
% 2.81/0.99  sim_joinable_simp:                      0
% 2.81/0.99  sim_ac_normalised:                      0
% 2.81/0.99  sim_smt_subsumption:                    0
% 2.81/0.99  
%------------------------------------------------------------------------------
