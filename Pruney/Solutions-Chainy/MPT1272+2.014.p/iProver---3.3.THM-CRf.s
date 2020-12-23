%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:20 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 297 expanded)
%              Number of clauses        :   82 ( 112 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   18
%              Number of atoms          :  367 (1008 expanded)
%              Number of equality atoms :   91 (  99 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0)
        & v3_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          & v3_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f36,f35])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_1(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
    | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_829,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_552,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_833,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_351])).

cnf(c_841,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
    | k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_830,plain,
    ( k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43
    | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_1084,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_43))) = k2_pre_topc(sK0,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_830])).

cnf(c_1785,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_43)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_43))
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_829,c_1084])).

cnf(c_5009,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_833,c_1785])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_43))) = k1_tops_1(sK0,X0_43) ),
    inference(subtyping,[status(esa)],[c_327])).

cnf(c_839,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_43))) = k1_tops_1(sK0,X0_43)
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_1367,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_833,c_839])).

cnf(c_5025,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_5009,c_1367])).

cnf(c_5257,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5025,c_841])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(k2_pre_topc(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_15,negated_conjecture,
    ( v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_240,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_241,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_243,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_241,c_17,c_16])).

cnf(c_254,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(sK0,sK1) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_243])).

cnf(c_255,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_257,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_17])).

cnf(c_258,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_259,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0_43,k2_tops_1(sK0,X0_43)) = k2_pre_topc(sK0,X0_43) ),
    inference(subtyping,[status(esa)],[c_291])).

cnf(c_590,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_595,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_597,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_604,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_606,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_884,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_556])).

cnf(c_885,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_884])).

cnf(c_560,plain,
    ( X0_43 != X1_43
    | k3_subset_1(X0_45,X0_43) = k3_subset_1(X0_45,X1_43) ),
    theory(equality)).

cnf(c_946,plain,
    ( X0_43 != k2_pre_topc(sK0,sK1)
    | k3_subset_1(u1_struct_0(sK0),X0_43) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_999,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k2_pre_topc(sK0,sK1)
    | k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_946])).

cnf(c_565,plain,
    ( ~ v1_tops_1(X0_43,X0_46)
    | v1_tops_1(X1_43,X0_46)
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_870,plain,
    ( ~ v1_tops_1(X0_43,sK0)
    | v1_tops_1(X1_43,sK0)
    | X1_43 != X0_43 ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_892,plain,
    ( v1_tops_1(X0_43,sK0)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | X0_43 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_914,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0_43),sK0)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | k3_subset_1(u1_struct_0(sK0),X0_43) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_892])).

cnf(c_1016,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),sK0)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_1017,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),sK0) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0_43,X0_44)
    | m1_subset_1(X1_43,X0_44)
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_1351,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != X0_43 ),
    inference(instantiation,[status(thm)],[c_561])).

cnf(c_2028,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_2029,plain,
    ( k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2028])).

cnf(c_2,plain,
    ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_554,plain,
    ( r1_tarski(k3_subset_1(X0_45,k4_subset_1(X0_45,X0_43,X1_43)),k3_subset_1(X0_45,X0_43))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2578,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_2579,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2578])).

cnf(c_13,plain,
    ( ~ v1_tops_1(X0,X1)
    | v1_tops_1(X2,X1)
    | ~ r1_tarski(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_271,plain,
    ( ~ v1_tops_1(X0,X1)
    | v1_tops_1(X2,X1)
    | ~ r1_tarski(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_272,plain,
    ( ~ v1_tops_1(X0,sK0)
    | v1_tops_1(X1,sK0)
    | ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_550,plain,
    ( ~ v1_tops_1(X0_43,sK0)
    | v1_tops_1(X1_43,sK0)
    | ~ r1_tarski(X0_43,X1_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_272])).

cnf(c_1165,plain,
    ( v1_tops_1(X0_43,sK0)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),sK0)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),X0_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_3129,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1165])).

cnf(c_3130,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),sK0) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3129])).

cnf(c_6632,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5257,c_16,c_19,c_21,c_259,c_590,c_597,c_606,c_885,c_999,c_1017,c_2029,c_2579,c_3130])).

cnf(c_6636,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_829,c_6632])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6636,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:57:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.63/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.01  
% 3.63/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/1.01  
% 3.63/1.01  ------  iProver source info
% 3.63/1.01  
% 3.63/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.63/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/1.01  git: non_committed_changes: false
% 3.63/1.01  git: last_make_outside_of_git: false
% 3.63/1.01  
% 3.63/1.01  ------ 
% 3.63/1.01  
% 3.63/1.01  ------ Input Options
% 3.63/1.01  
% 3.63/1.01  --out_options                           all
% 3.63/1.01  --tptp_safe_out                         true
% 3.63/1.01  --problem_path                          ""
% 3.63/1.01  --include_path                          ""
% 3.63/1.01  --clausifier                            res/vclausify_rel
% 3.63/1.01  --clausifier_options                    ""
% 3.63/1.01  --stdin                                 false
% 3.63/1.01  --stats_out                             all
% 3.63/1.01  
% 3.63/1.01  ------ General Options
% 3.63/1.01  
% 3.63/1.01  --fof                                   false
% 3.63/1.01  --time_out_real                         305.
% 3.63/1.01  --time_out_virtual                      -1.
% 3.63/1.01  --symbol_type_check                     false
% 3.63/1.01  --clausify_out                          false
% 3.63/1.01  --sig_cnt_out                           false
% 3.63/1.01  --trig_cnt_out                          false
% 3.63/1.01  --trig_cnt_out_tolerance                1.
% 3.63/1.01  --trig_cnt_out_sk_spl                   false
% 3.63/1.01  --abstr_cl_out                          false
% 3.63/1.01  
% 3.63/1.01  ------ Global Options
% 3.63/1.01  
% 3.63/1.01  --schedule                              default
% 3.63/1.01  --add_important_lit                     false
% 3.63/1.01  --prop_solver_per_cl                    1000
% 3.63/1.01  --min_unsat_core                        false
% 3.63/1.01  --soft_assumptions                      false
% 3.63/1.01  --soft_lemma_size                       3
% 3.63/1.01  --prop_impl_unit_size                   0
% 3.63/1.01  --prop_impl_unit                        []
% 3.63/1.01  --share_sel_clauses                     true
% 3.63/1.01  --reset_solvers                         false
% 3.63/1.01  --bc_imp_inh                            [conj_cone]
% 3.63/1.01  --conj_cone_tolerance                   3.
% 3.63/1.01  --extra_neg_conj                        none
% 3.63/1.01  --large_theory_mode                     true
% 3.63/1.01  --prolific_symb_bound                   200
% 3.63/1.01  --lt_threshold                          2000
% 3.63/1.01  --clause_weak_htbl                      true
% 3.63/1.01  --gc_record_bc_elim                     false
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing Options
% 3.63/1.01  
% 3.63/1.01  --preprocessing_flag                    true
% 3.63/1.01  --time_out_prep_mult                    0.1
% 3.63/1.01  --splitting_mode                        input
% 3.63/1.01  --splitting_grd                         true
% 3.63/1.01  --splitting_cvd                         false
% 3.63/1.01  --splitting_cvd_svl                     false
% 3.63/1.01  --splitting_nvd                         32
% 3.63/1.01  --sub_typing                            true
% 3.63/1.01  --prep_gs_sim                           true
% 3.63/1.01  --prep_unflatten                        true
% 3.63/1.01  --prep_res_sim                          true
% 3.63/1.01  --prep_upred                            true
% 3.63/1.01  --prep_sem_filter                       exhaustive
% 3.63/1.01  --prep_sem_filter_out                   false
% 3.63/1.01  --pred_elim                             true
% 3.63/1.01  --res_sim_input                         true
% 3.63/1.01  --eq_ax_congr_red                       true
% 3.63/1.01  --pure_diseq_elim                       true
% 3.63/1.01  --brand_transform                       false
% 3.63/1.01  --non_eq_to_eq                          false
% 3.63/1.01  --prep_def_merge                        true
% 3.63/1.01  --prep_def_merge_prop_impl              false
% 3.63/1.01  --prep_def_merge_mbd                    true
% 3.63/1.01  --prep_def_merge_tr_red                 false
% 3.63/1.01  --prep_def_merge_tr_cl                  false
% 3.63/1.01  --smt_preprocessing                     true
% 3.63/1.01  --smt_ac_axioms                         fast
% 3.63/1.01  --preprocessed_out                      false
% 3.63/1.01  --preprocessed_stats                    false
% 3.63/1.01  
% 3.63/1.01  ------ Abstraction refinement Options
% 3.63/1.01  
% 3.63/1.01  --abstr_ref                             []
% 3.63/1.01  --abstr_ref_prep                        false
% 3.63/1.01  --abstr_ref_until_sat                   false
% 3.63/1.01  --abstr_ref_sig_restrict                funpre
% 3.63/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/1.01  --abstr_ref_under                       []
% 3.63/1.01  
% 3.63/1.01  ------ SAT Options
% 3.63/1.01  
% 3.63/1.01  --sat_mode                              false
% 3.63/1.01  --sat_fm_restart_options                ""
% 3.63/1.01  --sat_gr_def                            false
% 3.63/1.01  --sat_epr_types                         true
% 3.63/1.01  --sat_non_cyclic_types                  false
% 3.63/1.01  --sat_finite_models                     false
% 3.63/1.01  --sat_fm_lemmas                         false
% 3.63/1.01  --sat_fm_prep                           false
% 3.63/1.01  --sat_fm_uc_incr                        true
% 3.63/1.01  --sat_out_model                         small
% 3.63/1.01  --sat_out_clauses                       false
% 3.63/1.01  
% 3.63/1.01  ------ QBF Options
% 3.63/1.01  
% 3.63/1.01  --qbf_mode                              false
% 3.63/1.01  --qbf_elim_univ                         false
% 3.63/1.01  --qbf_dom_inst                          none
% 3.63/1.01  --qbf_dom_pre_inst                      false
% 3.63/1.01  --qbf_sk_in                             false
% 3.63/1.01  --qbf_pred_elim                         true
% 3.63/1.01  --qbf_split                             512
% 3.63/1.01  
% 3.63/1.01  ------ BMC1 Options
% 3.63/1.01  
% 3.63/1.01  --bmc1_incremental                      false
% 3.63/1.01  --bmc1_axioms                           reachable_all
% 3.63/1.01  --bmc1_min_bound                        0
% 3.63/1.01  --bmc1_max_bound                        -1
% 3.63/1.01  --bmc1_max_bound_default                -1
% 3.63/1.01  --bmc1_symbol_reachability              true
% 3.63/1.01  --bmc1_property_lemmas                  false
% 3.63/1.01  --bmc1_k_induction                      false
% 3.63/1.01  --bmc1_non_equiv_states                 false
% 3.63/1.01  --bmc1_deadlock                         false
% 3.63/1.01  --bmc1_ucm                              false
% 3.63/1.01  --bmc1_add_unsat_core                   none
% 3.63/1.01  --bmc1_unsat_core_children              false
% 3.63/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/1.01  --bmc1_out_stat                         full
% 3.63/1.01  --bmc1_ground_init                      false
% 3.63/1.01  --bmc1_pre_inst_next_state              false
% 3.63/1.01  --bmc1_pre_inst_state                   false
% 3.63/1.01  --bmc1_pre_inst_reach_state             false
% 3.63/1.01  --bmc1_out_unsat_core                   false
% 3.63/1.01  --bmc1_aig_witness_out                  false
% 3.63/1.01  --bmc1_verbose                          false
% 3.63/1.01  --bmc1_dump_clauses_tptp                false
% 3.63/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.63/1.01  --bmc1_dump_file                        -
% 3.63/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.63/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.63/1.01  --bmc1_ucm_extend_mode                  1
% 3.63/1.01  --bmc1_ucm_init_mode                    2
% 3.63/1.01  --bmc1_ucm_cone_mode                    none
% 3.63/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.63/1.01  --bmc1_ucm_relax_model                  4
% 3.63/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.63/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/1.01  --bmc1_ucm_layered_model                none
% 3.63/1.01  --bmc1_ucm_max_lemma_size               10
% 3.63/1.01  
% 3.63/1.01  ------ AIG Options
% 3.63/1.01  
% 3.63/1.01  --aig_mode                              false
% 3.63/1.01  
% 3.63/1.01  ------ Instantiation Options
% 3.63/1.01  
% 3.63/1.01  --instantiation_flag                    true
% 3.63/1.01  --inst_sos_flag                         true
% 3.63/1.01  --inst_sos_phase                        true
% 3.63/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/1.01  --inst_lit_sel_side                     num_symb
% 3.63/1.01  --inst_solver_per_active                1400
% 3.63/1.01  --inst_solver_calls_frac                1.
% 3.63/1.01  --inst_passive_queue_type               priority_queues
% 3.63/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/1.01  --inst_passive_queues_freq              [25;2]
% 3.63/1.01  --inst_dismatching                      true
% 3.63/1.01  --inst_eager_unprocessed_to_passive     true
% 3.63/1.01  --inst_prop_sim_given                   true
% 3.63/1.01  --inst_prop_sim_new                     false
% 3.63/1.01  --inst_subs_new                         false
% 3.63/1.01  --inst_eq_res_simp                      false
% 3.63/1.01  --inst_subs_given                       false
% 3.63/1.01  --inst_orphan_elimination               true
% 3.63/1.01  --inst_learning_loop_flag               true
% 3.63/1.01  --inst_learning_start                   3000
% 3.63/1.01  --inst_learning_factor                  2
% 3.63/1.01  --inst_start_prop_sim_after_learn       3
% 3.63/1.01  --inst_sel_renew                        solver
% 3.63/1.01  --inst_lit_activity_flag                true
% 3.63/1.01  --inst_restr_to_given                   false
% 3.63/1.01  --inst_activity_threshold               500
% 3.63/1.01  --inst_out_proof                        true
% 3.63/1.01  
% 3.63/1.01  ------ Resolution Options
% 3.63/1.01  
% 3.63/1.01  --resolution_flag                       true
% 3.63/1.01  --res_lit_sel                           adaptive
% 3.63/1.01  --res_lit_sel_side                      none
% 3.63/1.01  --res_ordering                          kbo
% 3.63/1.01  --res_to_prop_solver                    active
% 3.63/1.01  --res_prop_simpl_new                    false
% 3.63/1.01  --res_prop_simpl_given                  true
% 3.63/1.01  --res_passive_queue_type                priority_queues
% 3.63/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/1.01  --res_passive_queues_freq               [15;5]
% 3.63/1.01  --res_forward_subs                      full
% 3.63/1.01  --res_backward_subs                     full
% 3.63/1.01  --res_forward_subs_resolution           true
% 3.63/1.01  --res_backward_subs_resolution          true
% 3.63/1.01  --res_orphan_elimination                true
% 3.63/1.01  --res_time_limit                        2.
% 3.63/1.01  --res_out_proof                         true
% 3.63/1.01  
% 3.63/1.01  ------ Superposition Options
% 3.63/1.01  
% 3.63/1.01  --superposition_flag                    true
% 3.63/1.01  --sup_passive_queue_type                priority_queues
% 3.63/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.63/1.01  --demod_completeness_check              fast
% 3.63/1.01  --demod_use_ground                      true
% 3.63/1.01  --sup_to_prop_solver                    passive
% 3.63/1.01  --sup_prop_simpl_new                    true
% 3.63/1.01  --sup_prop_simpl_given                  true
% 3.63/1.01  --sup_fun_splitting                     true
% 3.63/1.01  --sup_smt_interval                      50000
% 3.63/1.01  
% 3.63/1.01  ------ Superposition Simplification Setup
% 3.63/1.01  
% 3.63/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.63/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.63/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.63/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.63/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.63/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.63/1.01  --sup_immed_triv                        [TrivRules]
% 3.63/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_immed_bw_main                     []
% 3.63/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.63/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_input_bw                          []
% 3.63/1.01  
% 3.63/1.01  ------ Combination Options
% 3.63/1.01  
% 3.63/1.01  --comb_res_mult                         3
% 3.63/1.01  --comb_sup_mult                         2
% 3.63/1.01  --comb_inst_mult                        10
% 3.63/1.01  
% 3.63/1.01  ------ Debug Options
% 3.63/1.01  
% 3.63/1.01  --dbg_backtrace                         false
% 3.63/1.01  --dbg_dump_prop_clauses                 false
% 3.63/1.01  --dbg_dump_prop_clauses_file            -
% 3.63/1.01  --dbg_out_stat                          false
% 3.63/1.01  ------ Parsing...
% 3.63/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/1.01  ------ Proving...
% 3.63/1.01  ------ Problem Properties 
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  clauses                                 13
% 3.63/1.01  conjectures                             2
% 3.63/1.01  EPR                                     0
% 3.63/1.01  Horn                                    13
% 3.63/1.01  unary                                   2
% 3.63/1.01  binary                                  9
% 3.63/1.01  lits                                    28
% 3.63/1.01  lits eq                                 5
% 3.63/1.01  fd_pure                                 0
% 3.63/1.01  fd_pseudo                               0
% 3.63/1.01  fd_cond                                 0
% 3.63/1.01  fd_pseudo_cond                          0
% 3.63/1.01  AC symbols                              0
% 3.63/1.01  
% 3.63/1.01  ------ Schedule dynamic 5 is on 
% 3.63/1.01  
% 3.63/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  ------ 
% 3.63/1.01  Current options:
% 3.63/1.01  ------ 
% 3.63/1.01  
% 3.63/1.01  ------ Input Options
% 3.63/1.01  
% 3.63/1.01  --out_options                           all
% 3.63/1.01  --tptp_safe_out                         true
% 3.63/1.01  --problem_path                          ""
% 3.63/1.01  --include_path                          ""
% 3.63/1.01  --clausifier                            res/vclausify_rel
% 3.63/1.01  --clausifier_options                    ""
% 3.63/1.01  --stdin                                 false
% 3.63/1.01  --stats_out                             all
% 3.63/1.01  
% 3.63/1.01  ------ General Options
% 3.63/1.01  
% 3.63/1.01  --fof                                   false
% 3.63/1.01  --time_out_real                         305.
% 3.63/1.01  --time_out_virtual                      -1.
% 3.63/1.01  --symbol_type_check                     false
% 3.63/1.01  --clausify_out                          false
% 3.63/1.01  --sig_cnt_out                           false
% 3.63/1.01  --trig_cnt_out                          false
% 3.63/1.01  --trig_cnt_out_tolerance                1.
% 3.63/1.01  --trig_cnt_out_sk_spl                   false
% 3.63/1.01  --abstr_cl_out                          false
% 3.63/1.01  
% 3.63/1.01  ------ Global Options
% 3.63/1.01  
% 3.63/1.01  --schedule                              default
% 3.63/1.01  --add_important_lit                     false
% 3.63/1.01  --prop_solver_per_cl                    1000
% 3.63/1.01  --min_unsat_core                        false
% 3.63/1.01  --soft_assumptions                      false
% 3.63/1.01  --soft_lemma_size                       3
% 3.63/1.01  --prop_impl_unit_size                   0
% 3.63/1.01  --prop_impl_unit                        []
% 3.63/1.01  --share_sel_clauses                     true
% 3.63/1.01  --reset_solvers                         false
% 3.63/1.01  --bc_imp_inh                            [conj_cone]
% 3.63/1.01  --conj_cone_tolerance                   3.
% 3.63/1.01  --extra_neg_conj                        none
% 3.63/1.01  --large_theory_mode                     true
% 3.63/1.01  --prolific_symb_bound                   200
% 3.63/1.01  --lt_threshold                          2000
% 3.63/1.01  --clause_weak_htbl                      true
% 3.63/1.01  --gc_record_bc_elim                     false
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing Options
% 3.63/1.01  
% 3.63/1.01  --preprocessing_flag                    true
% 3.63/1.01  --time_out_prep_mult                    0.1
% 3.63/1.01  --splitting_mode                        input
% 3.63/1.01  --splitting_grd                         true
% 3.63/1.01  --splitting_cvd                         false
% 3.63/1.01  --splitting_cvd_svl                     false
% 3.63/1.01  --splitting_nvd                         32
% 3.63/1.01  --sub_typing                            true
% 3.63/1.01  --prep_gs_sim                           true
% 3.63/1.01  --prep_unflatten                        true
% 3.63/1.01  --prep_res_sim                          true
% 3.63/1.01  --prep_upred                            true
% 3.63/1.01  --prep_sem_filter                       exhaustive
% 3.63/1.01  --prep_sem_filter_out                   false
% 3.63/1.01  --pred_elim                             true
% 3.63/1.01  --res_sim_input                         true
% 3.63/1.01  --eq_ax_congr_red                       true
% 3.63/1.01  --pure_diseq_elim                       true
% 3.63/1.01  --brand_transform                       false
% 3.63/1.01  --non_eq_to_eq                          false
% 3.63/1.01  --prep_def_merge                        true
% 3.63/1.01  --prep_def_merge_prop_impl              false
% 3.63/1.01  --prep_def_merge_mbd                    true
% 3.63/1.01  --prep_def_merge_tr_red                 false
% 3.63/1.01  --prep_def_merge_tr_cl                  false
% 3.63/1.01  --smt_preprocessing                     true
% 3.63/1.01  --smt_ac_axioms                         fast
% 3.63/1.01  --preprocessed_out                      false
% 3.63/1.01  --preprocessed_stats                    false
% 3.63/1.01  
% 3.63/1.01  ------ Abstraction refinement Options
% 3.63/1.01  
% 3.63/1.01  --abstr_ref                             []
% 3.63/1.01  --abstr_ref_prep                        false
% 3.63/1.01  --abstr_ref_until_sat                   false
% 3.63/1.01  --abstr_ref_sig_restrict                funpre
% 3.63/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/1.01  --abstr_ref_under                       []
% 3.63/1.01  
% 3.63/1.01  ------ SAT Options
% 3.63/1.01  
% 3.63/1.01  --sat_mode                              false
% 3.63/1.01  --sat_fm_restart_options                ""
% 3.63/1.01  --sat_gr_def                            false
% 3.63/1.01  --sat_epr_types                         true
% 3.63/1.01  --sat_non_cyclic_types                  false
% 3.63/1.01  --sat_finite_models                     false
% 3.63/1.01  --sat_fm_lemmas                         false
% 3.63/1.01  --sat_fm_prep                           false
% 3.63/1.01  --sat_fm_uc_incr                        true
% 3.63/1.01  --sat_out_model                         small
% 3.63/1.01  --sat_out_clauses                       false
% 3.63/1.01  
% 3.63/1.01  ------ QBF Options
% 3.63/1.01  
% 3.63/1.01  --qbf_mode                              false
% 3.63/1.01  --qbf_elim_univ                         false
% 3.63/1.01  --qbf_dom_inst                          none
% 3.63/1.01  --qbf_dom_pre_inst                      false
% 3.63/1.01  --qbf_sk_in                             false
% 3.63/1.01  --qbf_pred_elim                         true
% 3.63/1.01  --qbf_split                             512
% 3.63/1.01  
% 3.63/1.01  ------ BMC1 Options
% 3.63/1.01  
% 3.63/1.01  --bmc1_incremental                      false
% 3.63/1.01  --bmc1_axioms                           reachable_all
% 3.63/1.01  --bmc1_min_bound                        0
% 3.63/1.01  --bmc1_max_bound                        -1
% 3.63/1.01  --bmc1_max_bound_default                -1
% 3.63/1.01  --bmc1_symbol_reachability              true
% 3.63/1.01  --bmc1_property_lemmas                  false
% 3.63/1.01  --bmc1_k_induction                      false
% 3.63/1.01  --bmc1_non_equiv_states                 false
% 3.63/1.01  --bmc1_deadlock                         false
% 3.63/1.01  --bmc1_ucm                              false
% 3.63/1.01  --bmc1_add_unsat_core                   none
% 3.63/1.01  --bmc1_unsat_core_children              false
% 3.63/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/1.01  --bmc1_out_stat                         full
% 3.63/1.01  --bmc1_ground_init                      false
% 3.63/1.01  --bmc1_pre_inst_next_state              false
% 3.63/1.01  --bmc1_pre_inst_state                   false
% 3.63/1.01  --bmc1_pre_inst_reach_state             false
% 3.63/1.01  --bmc1_out_unsat_core                   false
% 3.63/1.01  --bmc1_aig_witness_out                  false
% 3.63/1.01  --bmc1_verbose                          false
% 3.63/1.01  --bmc1_dump_clauses_tptp                false
% 3.63/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.63/1.01  --bmc1_dump_file                        -
% 3.63/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.63/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.63/1.01  --bmc1_ucm_extend_mode                  1
% 3.63/1.01  --bmc1_ucm_init_mode                    2
% 3.63/1.01  --bmc1_ucm_cone_mode                    none
% 3.63/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.63/1.01  --bmc1_ucm_relax_model                  4
% 3.63/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.63/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/1.01  --bmc1_ucm_layered_model                none
% 3.63/1.01  --bmc1_ucm_max_lemma_size               10
% 3.63/1.01  
% 3.63/1.01  ------ AIG Options
% 3.63/1.01  
% 3.63/1.01  --aig_mode                              false
% 3.63/1.01  
% 3.63/1.01  ------ Instantiation Options
% 3.63/1.01  
% 3.63/1.01  --instantiation_flag                    true
% 3.63/1.01  --inst_sos_flag                         true
% 3.63/1.01  --inst_sos_phase                        true
% 3.63/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/1.01  --inst_lit_sel_side                     none
% 3.63/1.01  --inst_solver_per_active                1400
% 3.63/1.01  --inst_solver_calls_frac                1.
% 3.63/1.01  --inst_passive_queue_type               priority_queues
% 3.63/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/1.01  --inst_passive_queues_freq              [25;2]
% 3.63/1.01  --inst_dismatching                      true
% 3.63/1.01  --inst_eager_unprocessed_to_passive     true
% 3.63/1.01  --inst_prop_sim_given                   true
% 3.63/1.01  --inst_prop_sim_new                     false
% 3.63/1.01  --inst_subs_new                         false
% 3.63/1.01  --inst_eq_res_simp                      false
% 3.63/1.01  --inst_subs_given                       false
% 3.63/1.01  --inst_orphan_elimination               true
% 3.63/1.01  --inst_learning_loop_flag               true
% 3.63/1.01  --inst_learning_start                   3000
% 3.63/1.01  --inst_learning_factor                  2
% 3.63/1.01  --inst_start_prop_sim_after_learn       3
% 3.63/1.01  --inst_sel_renew                        solver
% 3.63/1.01  --inst_lit_activity_flag                true
% 3.63/1.01  --inst_restr_to_given                   false
% 3.63/1.01  --inst_activity_threshold               500
% 3.63/1.01  --inst_out_proof                        true
% 3.63/1.01  
% 3.63/1.01  ------ Resolution Options
% 3.63/1.01  
% 3.63/1.01  --resolution_flag                       false
% 3.63/1.01  --res_lit_sel                           adaptive
% 3.63/1.01  --res_lit_sel_side                      none
% 3.63/1.01  --res_ordering                          kbo
% 3.63/1.01  --res_to_prop_solver                    active
% 3.63/1.01  --res_prop_simpl_new                    false
% 3.63/1.01  --res_prop_simpl_given                  true
% 3.63/1.01  --res_passive_queue_type                priority_queues
% 3.63/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/1.01  --res_passive_queues_freq               [15;5]
% 3.63/1.01  --res_forward_subs                      full
% 3.63/1.01  --res_backward_subs                     full
% 3.63/1.01  --res_forward_subs_resolution           true
% 3.63/1.01  --res_backward_subs_resolution          true
% 3.63/1.01  --res_orphan_elimination                true
% 3.63/1.01  --res_time_limit                        2.
% 3.63/1.01  --res_out_proof                         true
% 3.63/1.01  
% 3.63/1.01  ------ Superposition Options
% 3.63/1.01  
% 3.63/1.01  --superposition_flag                    true
% 3.63/1.01  --sup_passive_queue_type                priority_queues
% 3.63/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.63/1.01  --demod_completeness_check              fast
% 3.63/1.01  --demod_use_ground                      true
% 3.63/1.01  --sup_to_prop_solver                    passive
% 3.63/1.01  --sup_prop_simpl_new                    true
% 3.63/1.01  --sup_prop_simpl_given                  true
% 3.63/1.01  --sup_fun_splitting                     true
% 3.63/1.01  --sup_smt_interval                      50000
% 3.63/1.01  
% 3.63/1.01  ------ Superposition Simplification Setup
% 3.63/1.01  
% 3.63/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.63/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.63/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.63/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.63/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.63/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.63/1.01  --sup_immed_triv                        [TrivRules]
% 3.63/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_immed_bw_main                     []
% 3.63/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.63/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/1.01  --sup_input_bw                          []
% 3.63/1.01  
% 3.63/1.01  ------ Combination Options
% 3.63/1.01  
% 3.63/1.01  --comb_res_mult                         3
% 3.63/1.01  --comb_sup_mult                         2
% 3.63/1.01  --comb_inst_mult                        10
% 3.63/1.01  
% 3.63/1.01  ------ Debug Options
% 3.63/1.01  
% 3.63/1.01  --dbg_backtrace                         false
% 3.63/1.01  --dbg_dump_prop_clauses                 false
% 3.63/1.01  --dbg_dump_prop_clauses_file            -
% 3.63/1.01  --dbg_out_stat                          false
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  ------ Proving...
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  % SZS status Theorem for theBenchmark.p
% 3.63/1.01  
% 3.63/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/1.01  
% 3.63/1.01  fof(f1,axiom,(
% 3.63/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f15,plain,(
% 3.63/1.01    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.63/1.01    inference(ennf_transformation,[],[f1])).
% 3.63/1.01  
% 3.63/1.01  fof(f38,plain,(
% 3.63/1.01    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.63/1.01    inference(cnf_transformation,[],[f15])).
% 3.63/1.01  
% 3.63/1.01  fof(f13,conjecture,(
% 3.63/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f14,negated_conjecture,(
% 3.63/1.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.63/1.01    inference(negated_conjecture,[],[f13])).
% 3.63/1.01  
% 3.63/1.01  fof(f31,plain,(
% 3.63/1.01    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.63/1.01    inference(ennf_transformation,[],[f14])).
% 3.63/1.01  
% 3.63/1.01  fof(f32,plain,(
% 3.63/1.01    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.63/1.01    inference(flattening,[],[f31])).
% 3.63/1.01  
% 3.63/1.01  fof(f36,plain,(
% 3.63/1.01    ( ! [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_tops_1(k3_subset_1(u1_struct_0(X0),sK1),X0) & v3_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.63/1.01    introduced(choice_axiom,[])).
% 3.63/1.01  
% 3.63/1.01  fof(f35,plain,(
% 3.63/1.01    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.63/1.01    introduced(choice_axiom,[])).
% 3.63/1.01  
% 3.63/1.01  fof(f37,plain,(
% 3.63/1.01    (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.63/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f36,f35])).
% 3.63/1.01  
% 3.63/1.01  fof(f53,plain,(
% 3.63/1.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.63/1.01    inference(cnf_transformation,[],[f37])).
% 3.63/1.01  
% 3.63/1.01  fof(f4,axiom,(
% 3.63/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f18,plain,(
% 3.63/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.63/1.01    inference(ennf_transformation,[],[f4])).
% 3.63/1.01  
% 3.63/1.01  fof(f19,plain,(
% 3.63/1.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.63/1.01    inference(flattening,[],[f18])).
% 3.63/1.01  
% 3.63/1.01  fof(f41,plain,(
% 3.63/1.01    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f19])).
% 3.63/1.01  
% 3.63/1.01  fof(f52,plain,(
% 3.63/1.01    l1_pre_topc(sK0)),
% 3.63/1.01    inference(cnf_transformation,[],[f37])).
% 3.63/1.01  
% 3.63/1.01  fof(f2,axiom,(
% 3.63/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f16,plain,(
% 3.63/1.01    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.63/1.01    inference(ennf_transformation,[],[f2])).
% 3.63/1.01  
% 3.63/1.01  fof(f39,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.63/1.01    inference(cnf_transformation,[],[f16])).
% 3.63/1.01  
% 3.63/1.01  fof(f6,axiom,(
% 3.63/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f22,plain,(
% 3.63/1.01    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.63/1.01    inference(ennf_transformation,[],[f6])).
% 3.63/1.01  
% 3.63/1.01  fof(f43,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f22])).
% 3.63/1.01  
% 3.63/1.01  fof(f55,plain,(
% 3.63/1.01    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 3.63/1.01    inference(cnf_transformation,[],[f37])).
% 3.63/1.01  
% 3.63/1.01  fof(f7,axiom,(
% 3.63/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f23,plain,(
% 3.63/1.01    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.63/1.01    inference(ennf_transformation,[],[f7])).
% 3.63/1.01  
% 3.63/1.01  fof(f33,plain,(
% 3.63/1.01    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.63/1.01    inference(nnf_transformation,[],[f23])).
% 3.63/1.01  
% 3.63/1.01  fof(f44,plain,(
% 3.63/1.01    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f33])).
% 3.63/1.01  
% 3.63/1.01  fof(f8,axiom,(
% 3.63/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f24,plain,(
% 3.63/1.01    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.63/1.01    inference(ennf_transformation,[],[f8])).
% 3.63/1.01  
% 3.63/1.01  fof(f34,plain,(
% 3.63/1.01    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.63/1.01    inference(nnf_transformation,[],[f24])).
% 3.63/1.01  
% 3.63/1.01  fof(f46,plain,(
% 3.63/1.01    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f34])).
% 3.63/1.01  
% 3.63/1.01  fof(f54,plain,(
% 3.63/1.01    v3_tops_1(sK1,sK0)),
% 3.63/1.01    inference(cnf_transformation,[],[f37])).
% 3.63/1.01  
% 3.63/1.01  fof(f11,axiom,(
% 3.63/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f28,plain,(
% 3.63/1.01    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.63/1.01    inference(ennf_transformation,[],[f11])).
% 3.63/1.01  
% 3.63/1.01  fof(f50,plain,(
% 3.63/1.01    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f28])).
% 3.63/1.01  
% 3.63/1.01  fof(f9,axiom,(
% 3.63/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f25,plain,(
% 3.63/1.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.63/1.01    inference(ennf_transformation,[],[f9])).
% 3.63/1.01  
% 3.63/1.01  fof(f26,plain,(
% 3.63/1.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.63/1.01    inference(flattening,[],[f25])).
% 3.63/1.01  
% 3.63/1.01  fof(f48,plain,(
% 3.63/1.01    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f26])).
% 3.63/1.01  
% 3.63/1.01  fof(f3,axiom,(
% 3.63/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f17,plain,(
% 3.63/1.01    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.63/1.01    inference(ennf_transformation,[],[f3])).
% 3.63/1.01  
% 3.63/1.01  fof(f40,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.63/1.01    inference(cnf_transformation,[],[f17])).
% 3.63/1.01  
% 3.63/1.01  fof(f12,axiom,(
% 3.63/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 3.63/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.63/1.01  
% 3.63/1.01  fof(f29,plain,(
% 3.63/1.01    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.63/1.01    inference(ennf_transformation,[],[f12])).
% 3.63/1.01  
% 3.63/1.01  fof(f30,plain,(
% 3.63/1.01    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.63/1.01    inference(flattening,[],[f29])).
% 3.63/1.01  
% 3.63/1.01  fof(f51,plain,(
% 3.63/1.01    ( ! [X2,X0,X1] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.63/1.01    inference(cnf_transformation,[],[f30])).
% 3.63/1.01  
% 3.63/1.01  cnf(c_0,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.63/1.01      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.63/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_556,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
% 3.63/1.01      | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) ),
% 3.63/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_829,plain,
% 3.63/1.01      ( m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top
% 3.63/1.01      | m1_subset_1(k3_subset_1(X0_45,X0_43),k1_zfmisc_1(X0_45)) = iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_16,negated_conjecture,
% 3.63/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_552,negated_conjecture,
% 3.63/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_833,plain,
% 3.63/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_3,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | ~ l1_pre_topc(X1) ),
% 3.63/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_17,negated_conjecture,
% 3.63/1.01      ( l1_pre_topc(sK0) ),
% 3.63/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_350,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | sK0 != X1 ),
% 3.63/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_351,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(unflattening,[status(thm)],[c_350]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_544,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | m1_subset_1(k2_pre_topc(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(subtyping,[status(esa)],[c_351]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_841,plain,
% 3.63/1.01      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/1.01      | m1_subset_1(k2_pre_topc(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.63/1.01      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.63/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_555,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45))
% 3.63/1.01      | k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43 ),
% 3.63/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_830,plain,
% 3.63/1.01      ( k3_subset_1(X0_45,k3_subset_1(X0_45,X0_43)) = X0_43
% 3.63/1.01      | m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) != iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1084,plain,
% 3.63/1.01      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_43))) = k2_pre_topc(sK0,X0_43)
% 3.63/1.01      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_841,c_830]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1785,plain,
% 3.63/1.01      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_43)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_43))
% 3.63/1.01      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_829,c_1084]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_5009,plain,
% 3.63/1.01      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_833,c_1785]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_5,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | ~ l1_pre_topc(X1)
% 3.63/1.01      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.63/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_326,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 3.63/1.01      | sK0 != X1 ),
% 3.63/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_327,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.63/1.01      inference(unflattening,[status(thm)],[c_326]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_546,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_43))) = k1_tops_1(sK0,X0_43) ),
% 3.63/1.01      inference(subtyping,[status(esa)],[c_327]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_839,plain,
% 3.63/1.01      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_43))) = k1_tops_1(sK0,X0_43)
% 3.63/1.01      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1367,plain,
% 3.63/1.01      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_833,c_839]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_5025,plain,
% 3.63/1.01      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
% 3.63/1.01      inference(light_normalisation,[status(thm)],[c_5009,c_1367]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_5257,plain,
% 3.63/1.01      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.63/1.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_5025,c_841]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_19,plain,
% 3.63/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_14,negated_conjecture,
% 3.63/1.01      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 3.63/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_21,plain,
% 3.63/1.01      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) != iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_7,plain,
% 3.63/1.01      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 3.63/1.01      | ~ v2_tops_1(X1,X0)
% 3.63/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.63/1.01      | ~ l1_pre_topc(X0) ),
% 3.63/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_9,plain,
% 3.63/1.01      ( ~ v3_tops_1(X0,X1)
% 3.63/1.01      | v2_tops_1(k2_pre_topc(X1,X0),X1)
% 3.63/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | ~ l1_pre_topc(X1) ),
% 3.63/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_15,negated_conjecture,
% 3.63/1.01      ( v3_tops_1(sK1,sK0) ),
% 3.63/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_240,plain,
% 3.63/1.01      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 3.63/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.63/1.01      | ~ l1_pre_topc(X0)
% 3.63/1.01      | sK1 != X1
% 3.63/1.01      | sK0 != X0 ),
% 3.63/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_241,plain,
% 3.63/1.01      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 3.63/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | ~ l1_pre_topc(sK0) ),
% 3.63/1.01      inference(unflattening,[status(thm)],[c_240]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_243,plain,
% 3.63/1.01      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
% 3.63/1.01      inference(global_propositional_subsumption,
% 3.63/1.01                [status(thm)],
% 3.63/1.01                [c_241,c_17,c_16]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_254,plain,
% 3.63/1.01      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 3.63/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.63/1.01      | ~ l1_pre_topc(X0)
% 3.63/1.01      | k2_pre_topc(sK0,sK1) != X1
% 3.63/1.01      | sK0 != X0 ),
% 3.63/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_243]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_255,plain,
% 3.63/1.01      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
% 3.63/1.01      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | ~ l1_pre_topc(sK0) ),
% 3.63/1.01      inference(unflattening,[status(thm)],[c_254]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_257,plain,
% 3.63/1.01      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
% 3.63/1.01      inference(global_propositional_subsumption,
% 3.63/1.01                [status(thm)],
% 3.63/1.01                [c_255,c_17]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_258,plain,
% 3.63/1.01      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
% 3.63/1.01      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(renaming,[status(thm)],[c_257]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_259,plain,
% 3.63/1.01      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) = iProver_top
% 3.63/1.01      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_12,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | ~ l1_pre_topc(X1)
% 3.63/1.01      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.63/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_290,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 3.63/1.01      | sK0 != X1 ),
% 3.63/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_291,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 3.63/1.01      inference(unflattening,[status(thm)],[c_290]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_549,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | k4_subset_1(u1_struct_0(sK0),X0_43,k2_tops_1(sK0,X0_43)) = k2_pre_topc(sK0,X0_43) ),
% 3.63/1.01      inference(subtyping,[status(esa)],[c_291]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_590,plain,
% 3.63/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_549]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_10,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | ~ l1_pre_topc(X1) ),
% 3.63/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_314,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | sK0 != X1 ),
% 3.63/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_315,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(unflattening,[status(thm)],[c_314]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_547,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | m1_subset_1(k2_tops_1(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(subtyping,[status(esa)],[c_315]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_595,plain,
% 3.63/1.01      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/1.01      | m1_subset_1(k2_tops_1(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_597,plain,
% 3.63/1.01      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.63/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_595]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_604,plain,
% 3.63/1.01      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/1.01      | m1_subset_1(k2_pre_topc(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_606,plain,
% 3.63/1.01      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.63/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_604]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_884,plain,
% 3.63/1.01      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_556]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_885,plain,
% 3.63/1.01      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/1.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_884]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_560,plain,
% 3.63/1.01      ( X0_43 != X1_43
% 3.63/1.01      | k3_subset_1(X0_45,X0_43) = k3_subset_1(X0_45,X1_43) ),
% 3.63/1.01      theory(equality) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_946,plain,
% 3.63/1.01      ( X0_43 != k2_pre_topc(sK0,sK1)
% 3.63/1.01      | k3_subset_1(u1_struct_0(sK0),X0_43) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_560]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_999,plain,
% 3.63/1.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) != k2_pre_topc(sK0,sK1)
% 3.63/1.01      | k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_946]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_565,plain,
% 3.63/1.01      ( ~ v1_tops_1(X0_43,X0_46)
% 3.63/1.01      | v1_tops_1(X1_43,X0_46)
% 3.63/1.01      | X1_43 != X0_43 ),
% 3.63/1.01      theory(equality) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_870,plain,
% 3.63/1.01      ( ~ v1_tops_1(X0_43,sK0) | v1_tops_1(X1_43,sK0) | X1_43 != X0_43 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_565]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_892,plain,
% 3.63/1.01      ( v1_tops_1(X0_43,sK0)
% 3.63/1.01      | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
% 3.63/1.01      | X0_43 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_870]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_914,plain,
% 3.63/1.01      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0_43),sK0)
% 3.63/1.01      | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
% 3.63/1.01      | k3_subset_1(u1_struct_0(sK0),X0_43) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_892]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1016,plain,
% 3.63/1.01      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),sK0)
% 3.63/1.01      | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
% 3.63/1.01      | k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_914]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1017,plain,
% 3.63/1.01      ( k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
% 3.63/1.01      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),sK0) = iProver_top
% 3.63/1.01      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) != iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_561,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0_43,X0_44)
% 3.63/1.01      | m1_subset_1(X1_43,X0_44)
% 3.63/1.01      | X1_43 != X0_43 ),
% 3.63/1.01      theory(equality) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1351,plain,
% 3.63/1.01      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != X0_43 ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_561]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_2028,plain,
% 3.63/1.01      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_1351]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_2029,plain,
% 3.63/1.01      ( k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))
% 3.63/1.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.63/1.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_2028]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_2,plain,
% 3.63/1.01      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
% 3.63/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.63/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ),
% 3.63/1.01      inference(cnf_transformation,[],[f40]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_554,plain,
% 3.63/1.01      ( r1_tarski(k3_subset_1(X0_45,k4_subset_1(X0_45,X0_43,X1_43)),k3_subset_1(X0_45,X0_43))
% 3.63/1.01      | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_45))
% 3.63/1.01      | ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_45)) ),
% 3.63/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_2578,plain,
% 3.63/1.01      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
% 3.63/1.01      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_554]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_2579,plain,
% 3.63/1.01      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top
% 3.63/1.01      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_2578]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_13,plain,
% 3.63/1.01      ( ~ v1_tops_1(X0,X1)
% 3.63/1.01      | v1_tops_1(X2,X1)
% 3.63/1.01      | ~ r1_tarski(X0,X2)
% 3.63/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | ~ l1_pre_topc(X1) ),
% 3.63/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_271,plain,
% 3.63/1.01      ( ~ v1_tops_1(X0,X1)
% 3.63/1.01      | v1_tops_1(X2,X1)
% 3.63/1.01      | ~ r1_tarski(X0,X2)
% 3.63/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.63/1.01      | sK0 != X1 ),
% 3.63/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_272,plain,
% 3.63/1.01      ( ~ v1_tops_1(X0,sK0)
% 3.63/1.01      | v1_tops_1(X1,sK0)
% 3.63/1.01      | ~ r1_tarski(X0,X1)
% 3.63/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(unflattening,[status(thm)],[c_271]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_550,plain,
% 3.63/1.01      ( ~ v1_tops_1(X0_43,sK0)
% 3.63/1.01      | v1_tops_1(X1_43,sK0)
% 3.63/1.01      | ~ r1_tarski(X0_43,X1_43)
% 3.63/1.01      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(subtyping,[status(esa)],[c_272]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_1165,plain,
% 3.63/1.01      ( v1_tops_1(X0_43,sK0)
% 3.63/1.01      | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),sK0)
% 3.63/1.01      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),X0_43)
% 3.63/1.01      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_550]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_3129,plain,
% 3.63/1.01      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),sK0)
% 3.63/1.01      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 3.63/1.01      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1))
% 3.63/1.01      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.63/1.01      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.63/1.01      inference(instantiation,[status(thm)],[c_1165]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_3130,plain,
% 3.63/1.01      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),sK0) != iProver_top
% 3.63/1.01      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) = iProver_top
% 3.63/1.01      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
% 3.63/1.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.63/1.01      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(predicate_to_equality,[status(thm)],[c_3129]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_6632,plain,
% 3.63/1.01      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(global_propositional_subsumption,
% 3.63/1.01                [status(thm)],
% 3.63/1.01                [c_5257,c_16,c_19,c_21,c_259,c_590,c_597,c_606,c_885,
% 3.63/1.01                 c_999,c_1017,c_2029,c_2579,c_3130]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(c_6636,plain,
% 3.63/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.63/1.01      inference(superposition,[status(thm)],[c_829,c_6632]) ).
% 3.63/1.01  
% 3.63/1.01  cnf(contradiction,plain,
% 3.63/1.01      ( $false ),
% 3.63/1.01      inference(minisat,[status(thm)],[c_6636,c_19]) ).
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/1.01  
% 3.63/1.01  ------                               Statistics
% 3.63/1.01  
% 3.63/1.01  ------ General
% 3.63/1.01  
% 3.63/1.01  abstr_ref_over_cycles:                  0
% 3.63/1.01  abstr_ref_under_cycles:                 0
% 3.63/1.01  gc_basic_clause_elim:                   0
% 3.63/1.01  forced_gc_time:                         0
% 3.63/1.01  parsing_time:                           0.01
% 3.63/1.01  unif_index_cands_time:                  0.
% 3.63/1.01  unif_index_add_time:                    0.
% 3.63/1.01  orderings_time:                         0.
% 3.63/1.01  out_proof_time:                         0.011
% 3.63/1.01  total_time:                             0.324
% 3.63/1.01  num_of_symbols:                         47
% 3.63/1.01  num_of_terms:                           5071
% 3.63/1.01  
% 3.63/1.01  ------ Preprocessing
% 3.63/1.01  
% 3.63/1.01  num_of_splits:                          0
% 3.63/1.01  num_of_split_atoms:                     0
% 3.63/1.01  num_of_reused_defs:                     0
% 3.63/1.01  num_eq_ax_congr_red:                    19
% 3.63/1.01  num_of_sem_filtered_clauses:            1
% 3.63/1.01  num_of_subtypes:                        4
% 3.63/1.01  monotx_restored_types:                  0
% 3.63/1.01  sat_num_of_epr_types:                   0
% 3.63/1.01  sat_num_of_non_cyclic_types:            0
% 3.63/1.01  sat_guarded_non_collapsed_types:        1
% 3.63/1.01  num_pure_diseq_elim:                    0
% 3.63/1.01  simp_replaced_by:                       0
% 3.63/1.01  res_preprocessed:                       76
% 3.63/1.01  prep_upred:                             0
% 3.63/1.01  prep_unflattend:                        17
% 3.63/1.01  smt_new_axioms:                         0
% 3.63/1.01  pred_elim_cands:                        3
% 3.63/1.01  pred_elim:                              3
% 3.63/1.01  pred_elim_cl:                           5
% 3.63/1.01  pred_elim_cycles:                       6
% 3.63/1.01  merged_defs:                            0
% 3.63/1.01  merged_defs_ncl:                        0
% 3.63/1.01  bin_hyper_res:                          0
% 3.63/1.01  prep_cycles:                            4
% 3.63/1.01  pred_elim_time:                         0.005
% 3.63/1.01  splitting_time:                         0.
% 3.63/1.01  sem_filter_time:                        0.
% 3.63/1.01  monotx_time:                            0.
% 3.63/1.01  subtype_inf_time:                       0.
% 3.63/1.01  
% 3.63/1.01  ------ Problem properties
% 3.63/1.01  
% 3.63/1.01  clauses:                                13
% 3.63/1.01  conjectures:                            2
% 3.63/1.01  epr:                                    0
% 3.63/1.01  horn:                                   13
% 3.63/1.01  ground:                                 3
% 3.63/1.01  unary:                                  2
% 3.63/1.01  binary:                                 9
% 3.63/1.01  lits:                                   28
% 3.63/1.01  lits_eq:                                5
% 3.63/1.01  fd_pure:                                0
% 3.63/1.01  fd_pseudo:                              0
% 3.63/1.01  fd_cond:                                0
% 3.63/1.01  fd_pseudo_cond:                         0
% 3.63/1.01  ac_symbols:                             0
% 3.63/1.01  
% 3.63/1.01  ------ Propositional Solver
% 3.63/1.01  
% 3.63/1.01  prop_solver_calls:                      33
% 3.63/1.01  prop_fast_solver_calls:                 567
% 3.63/1.01  smt_solver_calls:                       0
% 3.63/1.01  smt_fast_solver_calls:                  0
% 3.63/1.01  prop_num_of_clauses:                    2115
% 3.63/1.01  prop_preprocess_simplified:             5715
% 3.63/1.01  prop_fo_subsumed:                       12
% 3.63/1.01  prop_solver_time:                       0.
% 3.63/1.01  smt_solver_time:                        0.
% 3.63/1.01  smt_fast_solver_time:                   0.
% 3.63/1.01  prop_fast_solver_time:                  0.
% 3.63/1.01  prop_unsat_core_time:                   0.
% 3.63/1.01  
% 3.63/1.01  ------ QBF
% 3.63/1.01  
% 3.63/1.01  qbf_q_res:                              0
% 3.63/1.01  qbf_num_tautologies:                    0
% 3.63/1.01  qbf_prep_cycles:                        0
% 3.63/1.01  
% 3.63/1.01  ------ BMC1
% 3.63/1.01  
% 3.63/1.01  bmc1_current_bound:                     -1
% 3.63/1.01  bmc1_last_solved_bound:                 -1
% 3.63/1.01  bmc1_unsat_core_size:                   -1
% 3.63/1.01  bmc1_unsat_core_parents_size:           -1
% 3.63/1.01  bmc1_merge_next_fun:                    0
% 3.63/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.63/1.01  
% 3.63/1.01  ------ Instantiation
% 3.63/1.01  
% 3.63/1.01  inst_num_of_clauses:                    878
% 3.63/1.01  inst_num_in_passive:                    436
% 3.63/1.01  inst_num_in_active:                     438
% 3.63/1.01  inst_num_in_unprocessed:                4
% 3.63/1.01  inst_num_of_loops:                      460
% 3.63/1.01  inst_num_of_learning_restarts:          0
% 3.63/1.01  inst_num_moves_active_passive:          16
% 3.63/1.01  inst_lit_activity:                      0
% 3.63/1.01  inst_lit_activity_moves:                0
% 3.63/1.01  inst_num_tautologies:                   0
% 3.63/1.01  inst_num_prop_implied:                  0
% 3.63/1.01  inst_num_existing_simplified:           0
% 3.63/1.01  inst_num_eq_res_simplified:             0
% 3.63/1.01  inst_num_child_elim:                    0
% 3.63/1.01  inst_num_of_dismatching_blockings:      1021
% 3.63/1.01  inst_num_of_non_proper_insts:           1461
% 3.63/1.01  inst_num_of_duplicates:                 0
% 3.63/1.01  inst_inst_num_from_inst_to_res:         0
% 3.63/1.01  inst_dismatching_checking_time:         0.
% 3.63/1.01  
% 3.63/1.01  ------ Resolution
% 3.63/1.01  
% 3.63/1.01  res_num_of_clauses:                     0
% 3.63/1.01  res_num_in_passive:                     0
% 3.63/1.01  res_num_in_active:                      0
% 3.63/1.01  res_num_of_loops:                       80
% 3.63/1.01  res_forward_subset_subsumed:            117
% 3.63/1.01  res_backward_subset_subsumed:           0
% 3.63/1.01  res_forward_subsumed:                   0
% 3.63/1.01  res_backward_subsumed:                  0
% 3.63/1.01  res_forward_subsumption_resolution:     0
% 3.63/1.01  res_backward_subsumption_resolution:    0
% 3.63/1.01  res_clause_to_clause_subsumption:       634
% 3.63/1.01  res_orphan_elimination:                 0
% 3.63/1.01  res_tautology_del:                      261
% 3.63/1.01  res_num_eq_res_simplified:              0
% 3.63/1.01  res_num_sel_changes:                    0
% 3.63/1.01  res_moves_from_active_to_pass:          0
% 3.63/1.01  
% 3.63/1.01  ------ Superposition
% 3.63/1.01  
% 3.63/1.01  sup_time_total:                         0.
% 3.63/1.01  sup_time_generating:                    0.
% 3.63/1.01  sup_time_sim_full:                      0.
% 3.63/1.01  sup_time_sim_immed:                     0.
% 3.63/1.01  
% 3.63/1.01  sup_num_of_clauses:                     247
% 3.63/1.01  sup_num_in_active:                      82
% 3.63/1.01  sup_num_in_passive:                     165
% 3.63/1.01  sup_num_of_loops:                       91
% 3.63/1.01  sup_fw_superposition:                   185
% 3.63/1.01  sup_bw_superposition:                   154
% 3.63/1.01  sup_immediate_simplified:               115
% 3.63/1.01  sup_given_eliminated:                   0
% 3.63/1.01  comparisons_done:                       0
% 3.63/1.01  comparisons_avoided:                    0
% 3.63/1.01  
% 3.63/1.01  ------ Simplifications
% 3.63/1.01  
% 3.63/1.01  
% 3.63/1.01  sim_fw_subset_subsumed:                 5
% 3.63/1.01  sim_bw_subset_subsumed:                 5
% 3.63/1.01  sim_fw_subsumed:                        2
% 3.63/1.01  sim_bw_subsumed:                        1
% 3.63/1.01  sim_fw_subsumption_res:                 0
% 3.63/1.01  sim_bw_subsumption_res:                 0
% 3.63/1.01  sim_tautology_del:                      4
% 3.63/1.01  sim_eq_tautology_del:                   68
% 3.63/1.01  sim_eq_res_simp:                        0
% 3.63/1.01  sim_fw_demodulated:                     22
% 3.63/1.01  sim_bw_demodulated:                     4
% 3.63/1.01  sim_light_normalised:                   88
% 3.63/1.01  sim_joinable_taut:                      0
% 3.63/1.01  sim_joinable_simp:                      0
% 3.63/1.01  sim_ac_normalised:                      0
% 3.63/1.01  sim_smt_subsumption:                    0
% 3.63/1.01  
%------------------------------------------------------------------------------
