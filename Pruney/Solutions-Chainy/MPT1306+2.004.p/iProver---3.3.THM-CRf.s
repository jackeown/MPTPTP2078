%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:30 EST 2020

% Result     : Theorem 8.04s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 287 expanded)
%              Number of clauses        :   69 ( 112 expanded)
%              Number of leaves         :   12 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  281 (1038 expanded)
%              Number of equality atoms :   96 ( 127 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0)
        & v2_tops_2(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0)
            & v2_tops_2(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v2_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v2_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tops_2(X1,X0)
              | ~ v2_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v2_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_335,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_620,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_336,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_619,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | m1_subset_1(k3_subset_1(X0_43,X0_41),k1_zfmisc_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_611,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(k3_subset_1(X0_43,X0_41),k1_zfmisc_1(X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k7_subset_1(X1,X2,X0)) = k4_subset_1(X1,k3_subset_1(X1,X2),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
    | k3_subset_1(X0_43,k7_subset_1(X0_43,X0_41,X1_41)) = k4_subset_1(X0_43,k3_subset_1(X0_43,X0_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_615,plain,
    ( k3_subset_1(X0_43,k7_subset_1(X0_43,X0_41,X1_41)) = k4_subset_1(X0_43,k3_subset_1(X0_43,X0_41),X1_41)
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_1826,plain,
    ( k3_subset_1(X0_43,k7_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41))) = k4_subset_1(X0_43,k3_subset_1(X0_43,X0_41),k3_subset_1(X0_43,X1_41))
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_615])).

cnf(c_29072,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_619,c_1826])).

cnf(c_30702,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) ),
    inference(superposition,[status(thm)],[c_620,c_29072])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
    | k9_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41)) = k7_subset_1(X0_43,X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_614,plain,
    ( k9_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41)) = k7_subset_1(X0_43,X0_41,X1_41)
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_1315,plain,
    ( k9_subset_1(X0_43,X0_41,k3_subset_1(X0_43,k3_subset_1(X0_43,X1_41))) = k7_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41))
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_614])).

cnf(c_13582,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
    | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_619,c_1315])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_342,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | k3_subset_1(X0_43,k3_subset_1(X0_43,X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_613,plain,
    ( k3_subset_1(X0_43,k3_subset_1(X0_43,X0_41)) = X0_41
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_1019,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_619,c_613])).

cnf(c_13653,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2)
    | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13582,c_1019])).

cnf(c_25234,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_620,c_13653])).

cnf(c_30796,plain,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_30702,c_25234])).

cnf(c_7,plain,
    ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_339,plain,
    ( r1_tarski(k3_subset_1(X0_43,k4_subset_1(X0_43,X0_41,X1_41)),k3_subset_1(X0_43,X0_41))
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_616,plain,
    ( r1_tarski(k3_subset_1(X0_43,k4_subset_1(X0_43,X0_41,X1_41)),k3_subset_1(X0_43,X0_41)) = iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_31108,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))) = iProver_top
    | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_30796,c_616])).

cnf(c_1020,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_620,c_613])).

cnf(c_31109,plain,
    ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31108,c_1020])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | k9_subset_1(X0_43,X0_41,X1_41) = k9_subset_1(X0_43,X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_610,plain,
    ( k9_subset_1(X0_43,X0_41,X1_41) = k9_subset_1(X0_43,X1_41,X0_41)
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_1187,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1) ),
    inference(superposition,[status(thm)],[c_620,c_610])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | m1_subset_1(k9_subset_1(X0_43,X1_41,X0_41),k1_zfmisc_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_612,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
    | m1_subset_1(k9_subset_1(X0_43,X1_41,X0_41),k1_zfmisc_1(X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_1506,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_612])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_731,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_732,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_5482,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1506,c_15,c_732])).

cnf(c_5489,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_5482])).

cnf(c_5905,plain,
    ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41))) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41) ),
    inference(superposition,[status(thm)],[c_5489,c_613])).

cnf(c_31110,plain,
    ( r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31109,c_5905])).

cnf(c_726,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_727,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_729,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_717,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_718,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_714,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_715,plain,
    ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_8,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_158,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_159,plain,
    ( ~ v2_tops_2(X0,sK0)
    | v2_tops_2(X1,sK0)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_334,plain,
    ( ~ v2_tops_2(X0_41,sK0)
    | v2_tops_2(X1_41,sK0)
    | ~ r1_tarski(X1_41,X0_41)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_159])).

cnf(c_709,plain,
    ( ~ v2_tops_2(X0_41,sK0)
    | v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | ~ r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_710,plain,
    ( v2_tops_2(X0_41,sK0) != iProver_top
    | v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) = iProver_top
    | r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),X0_41) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_712,plain,
    ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) = iProver_top
    | v2_tops_2(sK1,sK0) != iProver_top
    | r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) != iProver_top
    | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_9,negated_conjecture,
    ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,plain,
    ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( v2_tops_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31110,c_729,c_718,c_715,c_712,c_18,c_17,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:59:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.04/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.04/1.49  
% 8.04/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.04/1.49  
% 8.04/1.49  ------  iProver source info
% 8.04/1.49  
% 8.04/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.04/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.04/1.49  git: non_committed_changes: false
% 8.04/1.49  git: last_make_outside_of_git: false
% 8.04/1.49  
% 8.04/1.49  ------ 
% 8.04/1.49  
% 8.04/1.49  ------ Input Options
% 8.04/1.49  
% 8.04/1.49  --out_options                           all
% 8.04/1.49  --tptp_safe_out                         true
% 8.04/1.49  --problem_path                          ""
% 8.04/1.49  --include_path                          ""
% 8.04/1.49  --clausifier                            res/vclausify_rel
% 8.04/1.49  --clausifier_options                    --mode clausify
% 8.04/1.49  --stdin                                 false
% 8.04/1.49  --stats_out                             all
% 8.04/1.49  
% 8.04/1.49  ------ General Options
% 8.04/1.49  
% 8.04/1.49  --fof                                   false
% 8.04/1.49  --time_out_real                         305.
% 8.04/1.49  --time_out_virtual                      -1.
% 8.04/1.49  --symbol_type_check                     false
% 8.04/1.49  --clausify_out                          false
% 8.04/1.49  --sig_cnt_out                           false
% 8.04/1.49  --trig_cnt_out                          false
% 8.04/1.49  --trig_cnt_out_tolerance                1.
% 8.04/1.49  --trig_cnt_out_sk_spl                   false
% 8.04/1.49  --abstr_cl_out                          false
% 8.04/1.49  
% 8.04/1.49  ------ Global Options
% 8.04/1.49  
% 8.04/1.49  --schedule                              default
% 8.04/1.49  --add_important_lit                     false
% 8.04/1.49  --prop_solver_per_cl                    1000
% 8.04/1.49  --min_unsat_core                        false
% 8.04/1.49  --soft_assumptions                      false
% 8.04/1.49  --soft_lemma_size                       3
% 8.04/1.49  --prop_impl_unit_size                   0
% 8.04/1.49  --prop_impl_unit                        []
% 8.04/1.49  --share_sel_clauses                     true
% 8.04/1.49  --reset_solvers                         false
% 8.04/1.49  --bc_imp_inh                            [conj_cone]
% 8.04/1.49  --conj_cone_tolerance                   3.
% 8.04/1.49  --extra_neg_conj                        none
% 8.04/1.49  --large_theory_mode                     true
% 8.04/1.49  --prolific_symb_bound                   200
% 8.04/1.49  --lt_threshold                          2000
% 8.04/1.49  --clause_weak_htbl                      true
% 8.04/1.49  --gc_record_bc_elim                     false
% 8.04/1.49  
% 8.04/1.49  ------ Preprocessing Options
% 8.04/1.49  
% 8.04/1.49  --preprocessing_flag                    true
% 8.04/1.49  --time_out_prep_mult                    0.1
% 8.04/1.49  --splitting_mode                        input
% 8.04/1.49  --splitting_grd                         true
% 8.04/1.49  --splitting_cvd                         false
% 8.04/1.49  --splitting_cvd_svl                     false
% 8.04/1.49  --splitting_nvd                         32
% 8.04/1.49  --sub_typing                            true
% 8.04/1.49  --prep_gs_sim                           true
% 8.04/1.49  --prep_unflatten                        true
% 8.04/1.49  --prep_res_sim                          true
% 8.04/1.49  --prep_upred                            true
% 8.04/1.49  --prep_sem_filter                       exhaustive
% 8.04/1.49  --prep_sem_filter_out                   false
% 8.04/1.49  --pred_elim                             true
% 8.04/1.49  --res_sim_input                         true
% 8.04/1.49  --eq_ax_congr_red                       true
% 8.04/1.49  --pure_diseq_elim                       true
% 8.04/1.49  --brand_transform                       false
% 8.04/1.49  --non_eq_to_eq                          false
% 8.04/1.49  --prep_def_merge                        true
% 8.04/1.49  --prep_def_merge_prop_impl              false
% 8.04/1.49  --prep_def_merge_mbd                    true
% 8.04/1.49  --prep_def_merge_tr_red                 false
% 8.04/1.49  --prep_def_merge_tr_cl                  false
% 8.04/1.49  --smt_preprocessing                     true
% 8.04/1.49  --smt_ac_axioms                         fast
% 8.04/1.49  --preprocessed_out                      false
% 8.04/1.49  --preprocessed_stats                    false
% 8.04/1.49  
% 8.04/1.49  ------ Abstraction refinement Options
% 8.04/1.49  
% 8.04/1.49  --abstr_ref                             []
% 8.04/1.49  --abstr_ref_prep                        false
% 8.04/1.49  --abstr_ref_until_sat                   false
% 8.04/1.49  --abstr_ref_sig_restrict                funpre
% 8.04/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.04/1.49  --abstr_ref_under                       []
% 8.04/1.49  
% 8.04/1.49  ------ SAT Options
% 8.04/1.49  
% 8.04/1.49  --sat_mode                              false
% 8.04/1.49  --sat_fm_restart_options                ""
% 8.04/1.49  --sat_gr_def                            false
% 8.04/1.49  --sat_epr_types                         true
% 8.04/1.49  --sat_non_cyclic_types                  false
% 8.04/1.49  --sat_finite_models                     false
% 8.04/1.49  --sat_fm_lemmas                         false
% 8.04/1.49  --sat_fm_prep                           false
% 8.04/1.49  --sat_fm_uc_incr                        true
% 8.04/1.49  --sat_out_model                         small
% 8.04/1.49  --sat_out_clauses                       false
% 8.04/1.49  
% 8.04/1.49  ------ QBF Options
% 8.04/1.49  
% 8.04/1.49  --qbf_mode                              false
% 8.04/1.49  --qbf_elim_univ                         false
% 8.04/1.49  --qbf_dom_inst                          none
% 8.04/1.49  --qbf_dom_pre_inst                      false
% 8.04/1.49  --qbf_sk_in                             false
% 8.04/1.49  --qbf_pred_elim                         true
% 8.04/1.49  --qbf_split                             512
% 8.04/1.49  
% 8.04/1.49  ------ BMC1 Options
% 8.04/1.49  
% 8.04/1.49  --bmc1_incremental                      false
% 8.04/1.49  --bmc1_axioms                           reachable_all
% 8.04/1.49  --bmc1_min_bound                        0
% 8.04/1.49  --bmc1_max_bound                        -1
% 8.04/1.49  --bmc1_max_bound_default                -1
% 8.04/1.49  --bmc1_symbol_reachability              true
% 8.04/1.49  --bmc1_property_lemmas                  false
% 8.04/1.49  --bmc1_k_induction                      false
% 8.04/1.49  --bmc1_non_equiv_states                 false
% 8.04/1.49  --bmc1_deadlock                         false
% 8.04/1.49  --bmc1_ucm                              false
% 8.04/1.49  --bmc1_add_unsat_core                   none
% 8.04/1.49  --bmc1_unsat_core_children              false
% 8.04/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.04/1.49  --bmc1_out_stat                         full
% 8.04/1.49  --bmc1_ground_init                      false
% 8.04/1.49  --bmc1_pre_inst_next_state              false
% 8.04/1.49  --bmc1_pre_inst_state                   false
% 8.04/1.49  --bmc1_pre_inst_reach_state             false
% 8.04/1.49  --bmc1_out_unsat_core                   false
% 8.04/1.49  --bmc1_aig_witness_out                  false
% 8.04/1.49  --bmc1_verbose                          false
% 8.04/1.49  --bmc1_dump_clauses_tptp                false
% 8.04/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.04/1.49  --bmc1_dump_file                        -
% 8.04/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.04/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.04/1.49  --bmc1_ucm_extend_mode                  1
% 8.04/1.49  --bmc1_ucm_init_mode                    2
% 8.04/1.49  --bmc1_ucm_cone_mode                    none
% 8.04/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.04/1.49  --bmc1_ucm_relax_model                  4
% 8.04/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.04/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.04/1.49  --bmc1_ucm_layered_model                none
% 8.04/1.49  --bmc1_ucm_max_lemma_size               10
% 8.04/1.49  
% 8.04/1.49  ------ AIG Options
% 8.04/1.49  
% 8.04/1.49  --aig_mode                              false
% 8.04/1.49  
% 8.04/1.49  ------ Instantiation Options
% 8.04/1.49  
% 8.04/1.49  --instantiation_flag                    true
% 8.04/1.49  --inst_sos_flag                         false
% 8.04/1.49  --inst_sos_phase                        true
% 8.04/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.04/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.04/1.49  --inst_lit_sel_side                     num_symb
% 8.04/1.49  --inst_solver_per_active                1400
% 8.04/1.49  --inst_solver_calls_frac                1.
% 8.04/1.49  --inst_passive_queue_type               priority_queues
% 8.04/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.04/1.49  --inst_passive_queues_freq              [25;2]
% 8.04/1.49  --inst_dismatching                      true
% 8.04/1.49  --inst_eager_unprocessed_to_passive     true
% 8.04/1.49  --inst_prop_sim_given                   true
% 8.04/1.49  --inst_prop_sim_new                     false
% 8.04/1.49  --inst_subs_new                         false
% 8.04/1.49  --inst_eq_res_simp                      false
% 8.04/1.49  --inst_subs_given                       false
% 8.04/1.49  --inst_orphan_elimination               true
% 8.04/1.49  --inst_learning_loop_flag               true
% 8.04/1.49  --inst_learning_start                   3000
% 8.04/1.49  --inst_learning_factor                  2
% 8.04/1.49  --inst_start_prop_sim_after_learn       3
% 8.04/1.49  --inst_sel_renew                        solver
% 8.04/1.49  --inst_lit_activity_flag                true
% 8.04/1.49  --inst_restr_to_given                   false
% 8.04/1.49  --inst_activity_threshold               500
% 8.04/1.49  --inst_out_proof                        true
% 8.04/1.49  
% 8.04/1.49  ------ Resolution Options
% 8.04/1.49  
% 8.04/1.49  --resolution_flag                       true
% 8.04/1.49  --res_lit_sel                           adaptive
% 8.04/1.49  --res_lit_sel_side                      none
% 8.04/1.49  --res_ordering                          kbo
% 8.04/1.49  --res_to_prop_solver                    active
% 8.04/1.49  --res_prop_simpl_new                    false
% 8.04/1.49  --res_prop_simpl_given                  true
% 8.04/1.49  --res_passive_queue_type                priority_queues
% 8.04/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.04/1.49  --res_passive_queues_freq               [15;5]
% 8.04/1.49  --res_forward_subs                      full
% 8.04/1.49  --res_backward_subs                     full
% 8.04/1.49  --res_forward_subs_resolution           true
% 8.04/1.49  --res_backward_subs_resolution          true
% 8.04/1.49  --res_orphan_elimination                true
% 8.04/1.49  --res_time_limit                        2.
% 8.04/1.49  --res_out_proof                         true
% 8.04/1.49  
% 8.04/1.49  ------ Superposition Options
% 8.04/1.49  
% 8.04/1.49  --superposition_flag                    true
% 8.04/1.49  --sup_passive_queue_type                priority_queues
% 8.04/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.04/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.04/1.49  --demod_completeness_check              fast
% 8.04/1.49  --demod_use_ground                      true
% 8.04/1.49  --sup_to_prop_solver                    passive
% 8.04/1.49  --sup_prop_simpl_new                    true
% 8.04/1.49  --sup_prop_simpl_given                  true
% 8.04/1.49  --sup_fun_splitting                     false
% 8.04/1.49  --sup_smt_interval                      50000
% 8.04/1.49  
% 8.04/1.49  ------ Superposition Simplification Setup
% 8.04/1.49  
% 8.04/1.49  --sup_indices_passive                   []
% 8.04/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.04/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.49  --sup_full_bw                           [BwDemod]
% 8.04/1.49  --sup_immed_triv                        [TrivRules]
% 8.04/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.49  --sup_immed_bw_main                     []
% 8.04/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.04/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.04/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.04/1.49  
% 8.04/1.49  ------ Combination Options
% 8.04/1.49  
% 8.04/1.49  --comb_res_mult                         3
% 8.04/1.49  --comb_sup_mult                         2
% 8.04/1.49  --comb_inst_mult                        10
% 8.04/1.49  
% 8.04/1.49  ------ Debug Options
% 8.04/1.49  
% 8.04/1.49  --dbg_backtrace                         false
% 8.04/1.49  --dbg_dump_prop_clauses                 false
% 8.04/1.49  --dbg_dump_prop_clauses_file            -
% 8.04/1.49  --dbg_out_stat                          false
% 8.04/1.49  ------ Parsing...
% 8.04/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.04/1.49  
% 8.04/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 8.04/1.49  
% 8.04/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.04/1.49  
% 8.04/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.04/1.49  ------ Proving...
% 8.04/1.49  ------ Problem Properties 
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  clauses                                 13
% 8.04/1.49  conjectures                             4
% 8.04/1.49  EPR                                     1
% 8.04/1.49  Horn                                    13
% 8.04/1.49  unary                                   4
% 8.04/1.49  binary                                  4
% 8.04/1.49  lits                                    29
% 8.04/1.49  lits eq                                 5
% 8.04/1.49  fd_pure                                 0
% 8.04/1.49  fd_pseudo                               0
% 8.04/1.49  fd_cond                                 0
% 8.04/1.49  fd_pseudo_cond                          0
% 8.04/1.49  AC symbols                              0
% 8.04/1.49  
% 8.04/1.49  ------ Schedule dynamic 5 is on 
% 8.04/1.49  
% 8.04/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  ------ 
% 8.04/1.49  Current options:
% 8.04/1.49  ------ 
% 8.04/1.49  
% 8.04/1.49  ------ Input Options
% 8.04/1.49  
% 8.04/1.49  --out_options                           all
% 8.04/1.49  --tptp_safe_out                         true
% 8.04/1.49  --problem_path                          ""
% 8.04/1.49  --include_path                          ""
% 8.04/1.49  --clausifier                            res/vclausify_rel
% 8.04/1.49  --clausifier_options                    --mode clausify
% 8.04/1.49  --stdin                                 false
% 8.04/1.49  --stats_out                             all
% 8.04/1.49  
% 8.04/1.49  ------ General Options
% 8.04/1.49  
% 8.04/1.49  --fof                                   false
% 8.04/1.49  --time_out_real                         305.
% 8.04/1.49  --time_out_virtual                      -1.
% 8.04/1.49  --symbol_type_check                     false
% 8.04/1.49  --clausify_out                          false
% 8.04/1.49  --sig_cnt_out                           false
% 8.04/1.49  --trig_cnt_out                          false
% 8.04/1.49  --trig_cnt_out_tolerance                1.
% 8.04/1.49  --trig_cnt_out_sk_spl                   false
% 8.04/1.49  --abstr_cl_out                          false
% 8.04/1.49  
% 8.04/1.49  ------ Global Options
% 8.04/1.49  
% 8.04/1.49  --schedule                              default
% 8.04/1.49  --add_important_lit                     false
% 8.04/1.49  --prop_solver_per_cl                    1000
% 8.04/1.49  --min_unsat_core                        false
% 8.04/1.49  --soft_assumptions                      false
% 8.04/1.49  --soft_lemma_size                       3
% 8.04/1.49  --prop_impl_unit_size                   0
% 8.04/1.49  --prop_impl_unit                        []
% 8.04/1.49  --share_sel_clauses                     true
% 8.04/1.49  --reset_solvers                         false
% 8.04/1.49  --bc_imp_inh                            [conj_cone]
% 8.04/1.49  --conj_cone_tolerance                   3.
% 8.04/1.49  --extra_neg_conj                        none
% 8.04/1.49  --large_theory_mode                     true
% 8.04/1.49  --prolific_symb_bound                   200
% 8.04/1.49  --lt_threshold                          2000
% 8.04/1.49  --clause_weak_htbl                      true
% 8.04/1.49  --gc_record_bc_elim                     false
% 8.04/1.49  
% 8.04/1.49  ------ Preprocessing Options
% 8.04/1.49  
% 8.04/1.49  --preprocessing_flag                    true
% 8.04/1.49  --time_out_prep_mult                    0.1
% 8.04/1.49  --splitting_mode                        input
% 8.04/1.49  --splitting_grd                         true
% 8.04/1.49  --splitting_cvd                         false
% 8.04/1.49  --splitting_cvd_svl                     false
% 8.04/1.49  --splitting_nvd                         32
% 8.04/1.49  --sub_typing                            true
% 8.04/1.49  --prep_gs_sim                           true
% 8.04/1.49  --prep_unflatten                        true
% 8.04/1.49  --prep_res_sim                          true
% 8.04/1.49  --prep_upred                            true
% 8.04/1.49  --prep_sem_filter                       exhaustive
% 8.04/1.49  --prep_sem_filter_out                   false
% 8.04/1.49  --pred_elim                             true
% 8.04/1.49  --res_sim_input                         true
% 8.04/1.49  --eq_ax_congr_red                       true
% 8.04/1.49  --pure_diseq_elim                       true
% 8.04/1.49  --brand_transform                       false
% 8.04/1.49  --non_eq_to_eq                          false
% 8.04/1.49  --prep_def_merge                        true
% 8.04/1.49  --prep_def_merge_prop_impl              false
% 8.04/1.49  --prep_def_merge_mbd                    true
% 8.04/1.49  --prep_def_merge_tr_red                 false
% 8.04/1.49  --prep_def_merge_tr_cl                  false
% 8.04/1.49  --smt_preprocessing                     true
% 8.04/1.49  --smt_ac_axioms                         fast
% 8.04/1.49  --preprocessed_out                      false
% 8.04/1.49  --preprocessed_stats                    false
% 8.04/1.49  
% 8.04/1.49  ------ Abstraction refinement Options
% 8.04/1.49  
% 8.04/1.49  --abstr_ref                             []
% 8.04/1.49  --abstr_ref_prep                        false
% 8.04/1.49  --abstr_ref_until_sat                   false
% 8.04/1.49  --abstr_ref_sig_restrict                funpre
% 8.04/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.04/1.49  --abstr_ref_under                       []
% 8.04/1.49  
% 8.04/1.49  ------ SAT Options
% 8.04/1.49  
% 8.04/1.49  --sat_mode                              false
% 8.04/1.49  --sat_fm_restart_options                ""
% 8.04/1.49  --sat_gr_def                            false
% 8.04/1.49  --sat_epr_types                         true
% 8.04/1.49  --sat_non_cyclic_types                  false
% 8.04/1.49  --sat_finite_models                     false
% 8.04/1.49  --sat_fm_lemmas                         false
% 8.04/1.49  --sat_fm_prep                           false
% 8.04/1.49  --sat_fm_uc_incr                        true
% 8.04/1.49  --sat_out_model                         small
% 8.04/1.49  --sat_out_clauses                       false
% 8.04/1.49  
% 8.04/1.49  ------ QBF Options
% 8.04/1.49  
% 8.04/1.49  --qbf_mode                              false
% 8.04/1.49  --qbf_elim_univ                         false
% 8.04/1.49  --qbf_dom_inst                          none
% 8.04/1.49  --qbf_dom_pre_inst                      false
% 8.04/1.49  --qbf_sk_in                             false
% 8.04/1.49  --qbf_pred_elim                         true
% 8.04/1.49  --qbf_split                             512
% 8.04/1.49  
% 8.04/1.49  ------ BMC1 Options
% 8.04/1.49  
% 8.04/1.49  --bmc1_incremental                      false
% 8.04/1.49  --bmc1_axioms                           reachable_all
% 8.04/1.49  --bmc1_min_bound                        0
% 8.04/1.49  --bmc1_max_bound                        -1
% 8.04/1.49  --bmc1_max_bound_default                -1
% 8.04/1.49  --bmc1_symbol_reachability              true
% 8.04/1.49  --bmc1_property_lemmas                  false
% 8.04/1.49  --bmc1_k_induction                      false
% 8.04/1.49  --bmc1_non_equiv_states                 false
% 8.04/1.49  --bmc1_deadlock                         false
% 8.04/1.49  --bmc1_ucm                              false
% 8.04/1.49  --bmc1_add_unsat_core                   none
% 8.04/1.49  --bmc1_unsat_core_children              false
% 8.04/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.04/1.49  --bmc1_out_stat                         full
% 8.04/1.49  --bmc1_ground_init                      false
% 8.04/1.49  --bmc1_pre_inst_next_state              false
% 8.04/1.49  --bmc1_pre_inst_state                   false
% 8.04/1.49  --bmc1_pre_inst_reach_state             false
% 8.04/1.49  --bmc1_out_unsat_core                   false
% 8.04/1.49  --bmc1_aig_witness_out                  false
% 8.04/1.49  --bmc1_verbose                          false
% 8.04/1.49  --bmc1_dump_clauses_tptp                false
% 8.04/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.04/1.49  --bmc1_dump_file                        -
% 8.04/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.04/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.04/1.49  --bmc1_ucm_extend_mode                  1
% 8.04/1.49  --bmc1_ucm_init_mode                    2
% 8.04/1.49  --bmc1_ucm_cone_mode                    none
% 8.04/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.04/1.49  --bmc1_ucm_relax_model                  4
% 8.04/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.04/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.04/1.49  --bmc1_ucm_layered_model                none
% 8.04/1.49  --bmc1_ucm_max_lemma_size               10
% 8.04/1.49  
% 8.04/1.49  ------ AIG Options
% 8.04/1.49  
% 8.04/1.49  --aig_mode                              false
% 8.04/1.49  
% 8.04/1.49  ------ Instantiation Options
% 8.04/1.49  
% 8.04/1.49  --instantiation_flag                    true
% 8.04/1.49  --inst_sos_flag                         false
% 8.04/1.49  --inst_sos_phase                        true
% 8.04/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.04/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.04/1.49  --inst_lit_sel_side                     none
% 8.04/1.49  --inst_solver_per_active                1400
% 8.04/1.49  --inst_solver_calls_frac                1.
% 8.04/1.49  --inst_passive_queue_type               priority_queues
% 8.04/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.04/1.49  --inst_passive_queues_freq              [25;2]
% 8.04/1.49  --inst_dismatching                      true
% 8.04/1.49  --inst_eager_unprocessed_to_passive     true
% 8.04/1.49  --inst_prop_sim_given                   true
% 8.04/1.49  --inst_prop_sim_new                     false
% 8.04/1.49  --inst_subs_new                         false
% 8.04/1.49  --inst_eq_res_simp                      false
% 8.04/1.49  --inst_subs_given                       false
% 8.04/1.49  --inst_orphan_elimination               true
% 8.04/1.49  --inst_learning_loop_flag               true
% 8.04/1.49  --inst_learning_start                   3000
% 8.04/1.49  --inst_learning_factor                  2
% 8.04/1.49  --inst_start_prop_sim_after_learn       3
% 8.04/1.49  --inst_sel_renew                        solver
% 8.04/1.49  --inst_lit_activity_flag                true
% 8.04/1.49  --inst_restr_to_given                   false
% 8.04/1.49  --inst_activity_threshold               500
% 8.04/1.49  --inst_out_proof                        true
% 8.04/1.49  
% 8.04/1.49  ------ Resolution Options
% 8.04/1.49  
% 8.04/1.49  --resolution_flag                       false
% 8.04/1.49  --res_lit_sel                           adaptive
% 8.04/1.49  --res_lit_sel_side                      none
% 8.04/1.49  --res_ordering                          kbo
% 8.04/1.49  --res_to_prop_solver                    active
% 8.04/1.49  --res_prop_simpl_new                    false
% 8.04/1.49  --res_prop_simpl_given                  true
% 8.04/1.49  --res_passive_queue_type                priority_queues
% 8.04/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.04/1.49  --res_passive_queues_freq               [15;5]
% 8.04/1.49  --res_forward_subs                      full
% 8.04/1.49  --res_backward_subs                     full
% 8.04/1.49  --res_forward_subs_resolution           true
% 8.04/1.49  --res_backward_subs_resolution          true
% 8.04/1.49  --res_orphan_elimination                true
% 8.04/1.49  --res_time_limit                        2.
% 8.04/1.49  --res_out_proof                         true
% 8.04/1.49  
% 8.04/1.49  ------ Superposition Options
% 8.04/1.49  
% 8.04/1.49  --superposition_flag                    true
% 8.04/1.49  --sup_passive_queue_type                priority_queues
% 8.04/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.04/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.04/1.49  --demod_completeness_check              fast
% 8.04/1.49  --demod_use_ground                      true
% 8.04/1.49  --sup_to_prop_solver                    passive
% 8.04/1.49  --sup_prop_simpl_new                    true
% 8.04/1.49  --sup_prop_simpl_given                  true
% 8.04/1.49  --sup_fun_splitting                     false
% 8.04/1.49  --sup_smt_interval                      50000
% 8.04/1.49  
% 8.04/1.49  ------ Superposition Simplification Setup
% 8.04/1.49  
% 8.04/1.49  --sup_indices_passive                   []
% 8.04/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.04/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.49  --sup_full_bw                           [BwDemod]
% 8.04/1.49  --sup_immed_triv                        [TrivRules]
% 8.04/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.49  --sup_immed_bw_main                     []
% 8.04/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.04/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.04/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.04/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.04/1.49  
% 8.04/1.49  ------ Combination Options
% 8.04/1.49  
% 8.04/1.49  --comb_res_mult                         3
% 8.04/1.49  --comb_sup_mult                         2
% 8.04/1.49  --comb_inst_mult                        10
% 8.04/1.49  
% 8.04/1.49  ------ Debug Options
% 8.04/1.49  
% 8.04/1.49  --dbg_backtrace                         false
% 8.04/1.49  --dbg_dump_prop_clauses                 false
% 8.04/1.49  --dbg_dump_prop_clauses_file            -
% 8.04/1.49  --dbg_out_stat                          false
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  ------ Proving...
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  % SZS status Theorem for theBenchmark.p
% 8.04/1.49  
% 8.04/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.04/1.49  
% 8.04/1.49  fof(f10,conjecture,(
% 8.04/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f11,negated_conjecture,(
% 8.04/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 8.04/1.49    inference(negated_conjecture,[],[f10])).
% 8.04/1.49  
% 8.04/1.49  fof(f23,plain,(
% 8.04/1.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 8.04/1.49    inference(ennf_transformation,[],[f11])).
% 8.04/1.49  
% 8.04/1.49  fof(f24,plain,(
% 8.04/1.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 8.04/1.49    inference(flattening,[],[f23])).
% 8.04/1.49  
% 8.04/1.49  fof(f27,plain,(
% 8.04/1.49    ( ! [X0,X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0) & v2_tops_2(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 8.04/1.49    introduced(choice_axiom,[])).
% 8.04/1.49  
% 8.04/1.49  fof(f26,plain,(
% 8.04/1.49    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0) & v2_tops_2(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 8.04/1.49    introduced(choice_axiom,[])).
% 8.04/1.49  
% 8.04/1.49  fof(f25,plain,(
% 8.04/1.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v2_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 8.04/1.49    introduced(choice_axiom,[])).
% 8.04/1.49  
% 8.04/1.49  fof(f28,plain,(
% 8.04/1.49    ((~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v2_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 8.04/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 8.04/1.49  
% 8.04/1.49  fof(f39,plain,(
% 8.04/1.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 8.04/1.49    inference(cnf_transformation,[],[f28])).
% 8.04/1.49  
% 8.04/1.49  fof(f40,plain,(
% 8.04/1.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 8.04/1.49    inference(cnf_transformation,[],[f28])).
% 8.04/1.49  
% 8.04/1.49  fof(f3,axiom,(
% 8.04/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f15,plain,(
% 8.04/1.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f3])).
% 8.04/1.49  
% 8.04/1.49  fof(f31,plain,(
% 8.04/1.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.04/1.49    inference(cnf_transformation,[],[f15])).
% 8.04/1.49  
% 8.04/1.49  fof(f7,axiom,(
% 8.04/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f19,plain,(
% 8.04/1.49    ! [X0,X1] : (! [X2] : (k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f7])).
% 8.04/1.49  
% 8.04/1.49  fof(f35,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.04/1.49    inference(cnf_transformation,[],[f19])).
% 8.04/1.49  
% 8.04/1.49  fof(f6,axiom,(
% 8.04/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f18,plain,(
% 8.04/1.49    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f6])).
% 8.04/1.49  
% 8.04/1.49  fof(f34,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.04/1.49    inference(cnf_transformation,[],[f18])).
% 8.04/1.49  
% 8.04/1.49  fof(f5,axiom,(
% 8.04/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f17,plain,(
% 8.04/1.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f5])).
% 8.04/1.49  
% 8.04/1.49  fof(f33,plain,(
% 8.04/1.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.04/1.49    inference(cnf_transformation,[],[f17])).
% 8.04/1.49  
% 8.04/1.49  fof(f8,axiom,(
% 8.04/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f20,plain,(
% 8.04/1.49    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f8])).
% 8.04/1.49  
% 8.04/1.49  fof(f36,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.04/1.49    inference(cnf_transformation,[],[f20])).
% 8.04/1.49  
% 8.04/1.49  fof(f2,axiom,(
% 8.04/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f14,plain,(
% 8.04/1.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f2])).
% 8.04/1.49  
% 8.04/1.49  fof(f30,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 8.04/1.49    inference(cnf_transformation,[],[f14])).
% 8.04/1.49  
% 8.04/1.49  fof(f4,axiom,(
% 8.04/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f16,plain,(
% 8.04/1.49    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 8.04/1.49    inference(ennf_transformation,[],[f4])).
% 8.04/1.49  
% 8.04/1.49  fof(f32,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 8.04/1.49    inference(cnf_transformation,[],[f16])).
% 8.04/1.49  
% 8.04/1.49  fof(f9,axiom,(
% 8.04/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & r1_tarski(X1,X2)) => v2_tops_2(X1,X0)))))),
% 8.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.04/1.49  
% 8.04/1.49  fof(f21,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tops_2(X1,X0) | (~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 8.04/1.49    inference(ennf_transformation,[],[f9])).
% 8.04/1.49  
% 8.04/1.49  fof(f22,plain,(
% 8.04/1.49    ! [X0] : (! [X1] : (! [X2] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 8.04/1.49    inference(flattening,[],[f21])).
% 8.04/1.49  
% 8.04/1.49  fof(f37,plain,(
% 8.04/1.49    ( ! [X2,X0,X1] : (v2_tops_2(X1,X0) | ~v2_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 8.04/1.49    inference(cnf_transformation,[],[f22])).
% 8.04/1.49  
% 8.04/1.49  fof(f38,plain,(
% 8.04/1.49    l1_pre_topc(sK0)),
% 8.04/1.49    inference(cnf_transformation,[],[f28])).
% 8.04/1.49  
% 8.04/1.49  fof(f42,plain,(
% 8.04/1.49    ~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 8.04/1.49    inference(cnf_transformation,[],[f28])).
% 8.04/1.49  
% 8.04/1.49  fof(f41,plain,(
% 8.04/1.49    v2_tops_2(sK1,sK0)),
% 8.04/1.49    inference(cnf_transformation,[],[f28])).
% 8.04/1.49  
% 8.04/1.49  cnf(c_12,negated_conjecture,
% 8.04/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(cnf_transformation,[],[f39]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_335,negated_conjecture,
% 8.04/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_620,plain,
% 8.04/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_11,negated_conjecture,
% 8.04/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(cnf_transformation,[],[f40]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_336,negated_conjecture,
% 8.04/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_619,plain,
% 8.04/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_2,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.04/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 8.04/1.49      inference(cnf_transformation,[],[f31]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_344,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 8.04/1.49      | m1_subset_1(k3_subset_1(X0_43,X0_41),k1_zfmisc_1(X0_43)) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_611,plain,
% 8.04/1.49      ( m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
% 8.04/1.49      | m1_subset_1(k3_subset_1(X0_43,X0_41),k1_zfmisc_1(X0_43)) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_6,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.04/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 8.04/1.49      | k3_subset_1(X1,k7_subset_1(X1,X2,X0)) = k4_subset_1(X1,k3_subset_1(X1,X2),X0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f35]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_340,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 8.04/1.49      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
% 8.04/1.49      | k3_subset_1(X0_43,k7_subset_1(X0_43,X0_41,X1_41)) = k4_subset_1(X0_43,k3_subset_1(X0_43,X0_41),X1_41) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_615,plain,
% 8.04/1.49      ( k3_subset_1(X0_43,k7_subset_1(X0_43,X0_41,X1_41)) = k4_subset_1(X0_43,k3_subset_1(X0_43,X0_41),X1_41)
% 8.04/1.49      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1826,plain,
% 8.04/1.49      ( k3_subset_1(X0_43,k7_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41))) = k4_subset_1(X0_43,k3_subset_1(X0_43,X0_41),k3_subset_1(X0_43,X1_41))
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
% 8.04/1.49      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_611,c_615]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_29072,plain,
% 8.04/1.49      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_619,c_1826]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_30702,plain,
% 8.04/1.49      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_620,c_29072]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_5,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.04/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 8.04/1.49      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f34]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_341,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 8.04/1.49      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
% 8.04/1.49      | k9_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41)) = k7_subset_1(X0_43,X0_41,X1_41) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_614,plain,
% 8.04/1.49      ( k9_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41)) = k7_subset_1(X0_43,X0_41,X1_41)
% 8.04/1.49      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1315,plain,
% 8.04/1.49      ( k9_subset_1(X0_43,X0_41,k3_subset_1(X0_43,k3_subset_1(X0_43,X1_41))) = k7_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41))
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
% 8.04/1.49      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_611,c_614]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13582,plain,
% 8.04/1.49      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_619,c_1315]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_4,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.04/1.49      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 8.04/1.49      inference(cnf_transformation,[],[f33]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_342,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 8.04/1.49      | k3_subset_1(X0_43,k3_subset_1(X0_43,X0_41)) = X0_41 ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_613,plain,
% 8.04/1.49      ( k3_subset_1(X0_43,k3_subset_1(X0_43,X0_41)) = X0_41
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1019,plain,
% 8.04/1.49      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = sK2 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_619,c_613]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13653,plain,
% 8.04/1.49      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2)
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_13582,c_1019]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_25234,plain,
% 8.04/1.49      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_620,c_13653]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_30796,plain,
% 8.04/1.49      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_30702,c_25234]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_7,plain,
% 8.04/1.49      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
% 8.04/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 8.04/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
% 8.04/1.49      inference(cnf_transformation,[],[f36]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_339,plain,
% 8.04/1.49      ( r1_tarski(k3_subset_1(X0_43,k4_subset_1(X0_43,X0_41,X1_41)),k3_subset_1(X0_43,X0_41))
% 8.04/1.49      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
% 8.04/1.49      | ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_616,plain,
% 8.04/1.49      ( r1_tarski(k3_subset_1(X0_43,k4_subset_1(X0_43,X0_41,X1_41)),k3_subset_1(X0_43,X0_41)) = iProver_top
% 8.04/1.49      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_31108,plain,
% 8.04/1.49      ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))) = iProver_top
% 8.04/1.49      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 8.04/1.49      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_30796,c_616]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1020,plain,
% 8.04/1.49      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1 ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_620,c_613]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_31109,plain,
% 8.04/1.49      ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),sK1) = iProver_top
% 8.04/1.49      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 8.04/1.49      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(light_normalisation,[status(thm)],[c_31108,c_1020]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.04/1.49      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f30]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_345,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 8.04/1.49      | k9_subset_1(X0_43,X0_41,X1_41) = k9_subset_1(X0_43,X1_41,X0_41) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_610,plain,
% 8.04/1.49      ( k9_subset_1(X0_43,X0_41,X1_41) = k9_subset_1(X0_43,X1_41,X0_41)
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1187,plain,
% 8.04/1.49      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_620,c_610]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_3,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.04/1.49      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 8.04/1.49      inference(cnf_transformation,[],[f32]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_343,plain,
% 8.04/1.49      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 8.04/1.49      | m1_subset_1(k9_subset_1(X0_43,X1_41,X0_41),k1_zfmisc_1(X0_43)) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_612,plain,
% 8.04/1.49      ( m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
% 8.04/1.49      | m1_subset_1(k9_subset_1(X0_43,X1_41,X0_41),k1_zfmisc_1(X0_43)) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_1506,plain,
% 8.04/1.49      ( m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 8.04/1.49      | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_1187,c_612]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_15,plain,
% 8.04/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_731,plain,
% 8.04/1.49      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 8.04/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_343]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_732,plain,
% 8.04/1.49      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 8.04/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_5482,plain,
% 8.04/1.49      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 8.04/1.49      inference(global_propositional_subsumption,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_1506,c_15,c_732]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_5489,plain,
% 8.04/1.49      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_1187,c_5482]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_5905,plain,
% 8.04/1.49      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41))) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41) ),
% 8.04/1.49      inference(superposition,[status(thm)],[c_5489,c_613]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_31110,plain,
% 8.04/1.49      ( r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) = iProver_top
% 8.04/1.49      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 8.04/1.49      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(demodulation,[status(thm)],[c_31109,c_5905]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_726,plain,
% 8.04/1.49      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 8.04/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_343]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_727,plain,
% 8.04/1.49      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 8.04/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_729,plain,
% 8.04/1.49      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 8.04/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_727]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_717,plain,
% 8.04/1.49      ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 8.04/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_344]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_718,plain,
% 8.04/1.49      ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 8.04/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_714,plain,
% 8.04/1.49      ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 8.04/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_344]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_715,plain,
% 8.04/1.49      ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 8.04/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_8,plain,
% 8.04/1.49      ( ~ v2_tops_2(X0,X1)
% 8.04/1.49      | v2_tops_2(X2,X1)
% 8.04/1.49      | ~ r1_tarski(X2,X0)
% 8.04/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.04/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.04/1.49      | ~ l1_pre_topc(X1) ),
% 8.04/1.49      inference(cnf_transformation,[],[f37]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_13,negated_conjecture,
% 8.04/1.49      ( l1_pre_topc(sK0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f38]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_158,plain,
% 8.04/1.49      ( ~ v2_tops_2(X0,X1)
% 8.04/1.49      | v2_tops_2(X2,X1)
% 8.04/1.49      | ~ r1_tarski(X2,X0)
% 8.04/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.04/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 8.04/1.49      | sK0 != X1 ),
% 8.04/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_159,plain,
% 8.04/1.49      ( ~ v2_tops_2(X0,sK0)
% 8.04/1.49      | v2_tops_2(X1,sK0)
% 8.04/1.49      | ~ r1_tarski(X1,X0)
% 8.04/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 8.04/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(unflattening,[status(thm)],[c_158]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_334,plain,
% 8.04/1.49      ( ~ v2_tops_2(X0_41,sK0)
% 8.04/1.49      | v2_tops_2(X1_41,sK0)
% 8.04/1.49      | ~ r1_tarski(X1_41,X0_41)
% 8.04/1.49      | ~ m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 8.04/1.49      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(subtyping,[status(esa)],[c_159]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_709,plain,
% 8.04/1.49      ( ~ v2_tops_2(X0_41,sK0)
% 8.04/1.49      | v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
% 8.04/1.49      | ~ r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),X0_41)
% 8.04/1.49      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 8.04/1.49      | ~ m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_334]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_710,plain,
% 8.04/1.49      ( v2_tops_2(X0_41,sK0) != iProver_top
% 8.04/1.49      | v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) = iProver_top
% 8.04/1.49      | r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),X0_41) != iProver_top
% 8.04/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 8.04/1.49      | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_712,plain,
% 8.04/1.49      ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) = iProver_top
% 8.04/1.49      | v2_tops_2(sK1,sK0) != iProver_top
% 8.04/1.49      | r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) != iProver_top
% 8.04/1.49      | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 8.04/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 8.04/1.49      inference(instantiation,[status(thm)],[c_710]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_9,negated_conjecture,
% 8.04/1.49      ( ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f42]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_18,plain,
% 8.04/1.49      ( v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_10,negated_conjecture,
% 8.04/1.49      ( v2_tops_2(sK1,sK0) ),
% 8.04/1.49      inference(cnf_transformation,[],[f41]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_17,plain,
% 8.04/1.49      ( v2_tops_2(sK1,sK0) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(c_16,plain,
% 8.04/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 8.04/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.04/1.49  
% 8.04/1.49  cnf(contradiction,plain,
% 8.04/1.49      ( $false ),
% 8.04/1.49      inference(minisat,
% 8.04/1.49                [status(thm)],
% 8.04/1.49                [c_31110,c_729,c_718,c_715,c_712,c_18,c_17,c_16,c_15]) ).
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.04/1.49  
% 8.04/1.49  ------                               Statistics
% 8.04/1.49  
% 8.04/1.49  ------ General
% 8.04/1.49  
% 8.04/1.49  abstr_ref_over_cycles:                  0
% 8.04/1.49  abstr_ref_under_cycles:                 0
% 8.04/1.49  gc_basic_clause_elim:                   0
% 8.04/1.49  forced_gc_time:                         0
% 8.04/1.49  parsing_time:                           0.009
% 8.04/1.49  unif_index_cands_time:                  0.
% 8.04/1.49  unif_index_add_time:                    0.
% 8.04/1.49  orderings_time:                         0.
% 8.04/1.49  out_proof_time:                         0.01
% 8.04/1.49  total_time:                             0.952
% 8.04/1.49  num_of_symbols:                         44
% 8.04/1.49  num_of_terms:                           33571
% 8.04/1.49  
% 8.04/1.49  ------ Preprocessing
% 8.04/1.49  
% 8.04/1.49  num_of_splits:                          0
% 8.04/1.49  num_of_split_atoms:                     0
% 8.04/1.49  num_of_reused_defs:                     0
% 8.04/1.49  num_eq_ax_congr_red:                    23
% 8.04/1.49  num_of_sem_filtered_clauses:            1
% 8.04/1.49  num_of_subtypes:                        3
% 8.04/1.49  monotx_restored_types:                  0
% 8.04/1.49  sat_num_of_epr_types:                   0
% 8.04/1.49  sat_num_of_non_cyclic_types:            0
% 8.04/1.49  sat_guarded_non_collapsed_types:        1
% 8.04/1.49  num_pure_diseq_elim:                    0
% 8.04/1.49  simp_replaced_by:                       0
% 8.04/1.49  res_preprocessed:                       70
% 8.04/1.49  prep_upred:                             0
% 8.04/1.49  prep_unflattend:                        5
% 8.04/1.49  smt_new_axioms:                         0
% 8.04/1.49  pred_elim_cands:                        3
% 8.04/1.49  pred_elim:                              1
% 8.04/1.49  pred_elim_cl:                           1
% 8.04/1.49  pred_elim_cycles:                       3
% 8.04/1.49  merged_defs:                            0
% 8.04/1.49  merged_defs_ncl:                        0
% 8.04/1.49  bin_hyper_res:                          0
% 8.04/1.49  prep_cycles:                            4
% 8.04/1.49  pred_elim_time:                         0.002
% 8.04/1.49  splitting_time:                         0.
% 8.04/1.49  sem_filter_time:                        0.
% 8.04/1.49  monotx_time:                            0.
% 8.04/1.49  subtype_inf_time:                       0.
% 8.04/1.49  
% 8.04/1.49  ------ Problem properties
% 8.04/1.49  
% 8.04/1.49  clauses:                                13
% 8.04/1.49  conjectures:                            4
% 8.04/1.49  epr:                                    1
% 8.04/1.49  horn:                                   13
% 8.04/1.49  ground:                                 4
% 8.04/1.49  unary:                                  4
% 8.04/1.49  binary:                                 4
% 8.04/1.49  lits:                                   29
% 8.04/1.49  lits_eq:                                5
% 8.04/1.49  fd_pure:                                0
% 8.04/1.49  fd_pseudo:                              0
% 8.04/1.49  fd_cond:                                0
% 8.04/1.49  fd_pseudo_cond:                         0
% 8.04/1.49  ac_symbols:                             0
% 8.04/1.49  
% 8.04/1.49  ------ Propositional Solver
% 8.04/1.49  
% 8.04/1.49  prop_solver_calls:                      30
% 8.04/1.49  prop_fast_solver_calls:                 680
% 8.04/1.49  smt_solver_calls:                       0
% 8.04/1.49  smt_fast_solver_calls:                  0
% 8.04/1.49  prop_num_of_clauses:                    9787
% 8.04/1.49  prop_preprocess_simplified:             12740
% 8.04/1.49  prop_fo_subsumed:                       5
% 8.04/1.49  prop_solver_time:                       0.
% 8.04/1.49  smt_solver_time:                        0.
% 8.04/1.49  smt_fast_solver_time:                   0.
% 8.04/1.49  prop_fast_solver_time:                  0.
% 8.04/1.49  prop_unsat_core_time:                   0.001
% 8.04/1.49  
% 8.04/1.49  ------ QBF
% 8.04/1.49  
% 8.04/1.49  qbf_q_res:                              0
% 8.04/1.49  qbf_num_tautologies:                    0
% 8.04/1.49  qbf_prep_cycles:                        0
% 8.04/1.49  
% 8.04/1.49  ------ BMC1
% 8.04/1.49  
% 8.04/1.49  bmc1_current_bound:                     -1
% 8.04/1.49  bmc1_last_solved_bound:                 -1
% 8.04/1.49  bmc1_unsat_core_size:                   -1
% 8.04/1.49  bmc1_unsat_core_parents_size:           -1
% 8.04/1.49  bmc1_merge_next_fun:                    0
% 8.04/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.04/1.49  
% 8.04/1.49  ------ Instantiation
% 8.04/1.49  
% 8.04/1.49  inst_num_of_clauses:                    2051
% 8.04/1.49  inst_num_in_passive:                    537
% 8.04/1.49  inst_num_in_active:                     983
% 8.04/1.49  inst_num_in_unprocessed:                531
% 8.04/1.49  inst_num_of_loops:                      1040
% 8.04/1.49  inst_num_of_learning_restarts:          0
% 8.04/1.49  inst_num_moves_active_passive:          53
% 8.04/1.49  inst_lit_activity:                      0
% 8.04/1.49  inst_lit_activity_moves:                0
% 8.04/1.49  inst_num_tautologies:                   0
% 8.04/1.49  inst_num_prop_implied:                  0
% 8.04/1.49  inst_num_existing_simplified:           0
% 8.04/1.49  inst_num_eq_res_simplified:             0
% 8.04/1.49  inst_num_child_elim:                    0
% 8.04/1.49  inst_num_of_dismatching_blockings:      2854
% 8.04/1.49  inst_num_of_non_proper_insts:           2454
% 8.04/1.49  inst_num_of_duplicates:                 0
% 8.04/1.49  inst_inst_num_from_inst_to_res:         0
% 8.04/1.49  inst_dismatching_checking_time:         0.
% 8.04/1.49  
% 8.04/1.49  ------ Resolution
% 8.04/1.49  
% 8.04/1.49  res_num_of_clauses:                     0
% 8.04/1.49  res_num_in_passive:                     0
% 8.04/1.49  res_num_in_active:                      0
% 8.04/1.49  res_num_of_loops:                       74
% 8.04/1.49  res_forward_subset_subsumed:            162
% 8.04/1.49  res_backward_subset_subsumed:           4
% 8.04/1.49  res_forward_subsumed:                   0
% 8.04/1.49  res_backward_subsumed:                  0
% 8.04/1.49  res_forward_subsumption_resolution:     0
% 8.04/1.49  res_backward_subsumption_resolution:    0
% 8.04/1.49  res_clause_to_clause_subsumption:       11199
% 8.04/1.49  res_orphan_elimination:                 0
% 8.04/1.49  res_tautology_del:                      500
% 8.04/1.49  res_num_eq_res_simplified:              0
% 8.04/1.49  res_num_sel_changes:                    0
% 8.04/1.49  res_moves_from_active_to_pass:          0
% 8.04/1.49  
% 8.04/1.49  ------ Superposition
% 8.04/1.49  
% 8.04/1.49  sup_time_total:                         0.
% 8.04/1.49  sup_time_generating:                    0.
% 8.04/1.49  sup_time_sim_full:                      0.
% 8.04/1.49  sup_time_sim_immed:                     0.
% 8.04/1.49  
% 8.04/1.49  sup_num_of_clauses:                     2103
% 8.04/1.49  sup_num_in_active:                      207
% 8.04/1.49  sup_num_in_passive:                     1896
% 8.04/1.49  sup_num_of_loops:                       206
% 8.04/1.49  sup_fw_superposition:                   2504
% 8.04/1.49  sup_bw_superposition:                   2201
% 8.04/1.49  sup_immediate_simplified:               1283
% 8.04/1.49  sup_given_eliminated:                   0
% 8.04/1.49  comparisons_done:                       0
% 8.04/1.49  comparisons_avoided:                    0
% 8.04/1.49  
% 8.04/1.49  ------ Simplifications
% 8.04/1.49  
% 8.04/1.49  
% 8.04/1.49  sim_fw_subset_subsumed:                 125
% 8.04/1.49  sim_bw_subset_subsumed:                 79
% 8.04/1.49  sim_fw_subsumed:                        395
% 8.04/1.49  sim_bw_subsumed:                        95
% 8.04/1.49  sim_fw_subsumption_res:                 0
% 8.04/1.49  sim_bw_subsumption_res:                 0
% 8.04/1.49  sim_tautology_del:                      2
% 8.04/1.49  sim_eq_tautology_del:                   114
% 8.04/1.49  sim_eq_res_simp:                        0
% 8.04/1.49  sim_fw_demodulated:                     184
% 8.04/1.49  sim_bw_demodulated:                     53
% 8.04/1.49  sim_light_normalised:                   501
% 8.04/1.49  sim_joinable_taut:                      0
% 8.04/1.49  sim_joinable_simp:                      0
% 8.04/1.49  sim_ac_normalised:                      0
% 8.04/1.49  sim_smt_subsumption:                    0
% 8.04/1.49  
%------------------------------------------------------------------------------
