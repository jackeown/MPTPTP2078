%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:22 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
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
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0)
            & v1_tops_2(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    v1_tops_2(sK1,sK0) ),
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
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_158,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_159,plain,
    ( ~ v1_tops_2(X0,sK0)
    | v1_tops_2(X1,sK0)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_334,plain,
    ( ~ v1_tops_2(X0_41,sK0)
    | v1_tops_2(X1_41,sK0)
    | ~ r1_tarski(X1_41,X0_41)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_159])).

cnf(c_709,plain,
    ( ~ v1_tops_2(X0_41,sK0)
    | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | ~ r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),X0_41)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_710,plain,
    ( v1_tops_2(X0_41,sK0) != iProver_top
    | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) = iProver_top
    | r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),X0_41) != iProver_top
    | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_712,plain,
    ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) = iProver_top
    | v1_tops_2(sK1,sK0) != iProver_top
    | r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) != iProver_top
    | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_9,negated_conjecture,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,plain,
    ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,plain,
    ( v1_tops_2(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31110,c_729,c_718,c_715,c_712,c_18,c_17,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:46:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.78/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/1.50  
% 7.78/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.78/1.50  
% 7.78/1.50  ------  iProver source info
% 7.78/1.50  
% 7.78/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.78/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.78/1.50  git: non_committed_changes: false
% 7.78/1.50  git: last_make_outside_of_git: false
% 7.78/1.50  
% 7.78/1.50  ------ 
% 7.78/1.50  
% 7.78/1.50  ------ Input Options
% 7.78/1.50  
% 7.78/1.50  --out_options                           all
% 7.78/1.50  --tptp_safe_out                         true
% 7.78/1.50  --problem_path                          ""
% 7.78/1.50  --include_path                          ""
% 7.78/1.50  --clausifier                            res/vclausify_rel
% 7.78/1.50  --clausifier_options                    --mode clausify
% 7.78/1.50  --stdin                                 false
% 7.78/1.50  --stats_out                             all
% 7.78/1.50  
% 7.78/1.50  ------ General Options
% 7.78/1.50  
% 7.78/1.50  --fof                                   false
% 7.78/1.50  --time_out_real                         305.
% 7.78/1.50  --time_out_virtual                      -1.
% 7.78/1.50  --symbol_type_check                     false
% 7.78/1.50  --clausify_out                          false
% 7.78/1.50  --sig_cnt_out                           false
% 7.78/1.50  --trig_cnt_out                          false
% 7.78/1.50  --trig_cnt_out_tolerance                1.
% 7.78/1.50  --trig_cnt_out_sk_spl                   false
% 7.78/1.50  --abstr_cl_out                          false
% 7.78/1.50  
% 7.78/1.50  ------ Global Options
% 7.78/1.50  
% 7.78/1.50  --schedule                              default
% 7.78/1.50  --add_important_lit                     false
% 7.78/1.50  --prop_solver_per_cl                    1000
% 7.78/1.50  --min_unsat_core                        false
% 7.78/1.50  --soft_assumptions                      false
% 7.78/1.50  --soft_lemma_size                       3
% 7.78/1.50  --prop_impl_unit_size                   0
% 7.78/1.50  --prop_impl_unit                        []
% 7.78/1.50  --share_sel_clauses                     true
% 7.78/1.50  --reset_solvers                         false
% 7.78/1.50  --bc_imp_inh                            [conj_cone]
% 7.78/1.50  --conj_cone_tolerance                   3.
% 7.78/1.50  --extra_neg_conj                        none
% 7.78/1.50  --large_theory_mode                     true
% 7.78/1.50  --prolific_symb_bound                   200
% 7.78/1.50  --lt_threshold                          2000
% 7.78/1.50  --clause_weak_htbl                      true
% 7.78/1.50  --gc_record_bc_elim                     false
% 7.78/1.50  
% 7.78/1.50  ------ Preprocessing Options
% 7.78/1.50  
% 7.78/1.50  --preprocessing_flag                    true
% 7.78/1.50  --time_out_prep_mult                    0.1
% 7.78/1.50  --splitting_mode                        input
% 7.78/1.50  --splitting_grd                         true
% 7.78/1.50  --splitting_cvd                         false
% 7.78/1.50  --splitting_cvd_svl                     false
% 7.78/1.50  --splitting_nvd                         32
% 7.78/1.50  --sub_typing                            true
% 7.78/1.50  --prep_gs_sim                           true
% 7.78/1.50  --prep_unflatten                        true
% 7.78/1.50  --prep_res_sim                          true
% 7.78/1.50  --prep_upred                            true
% 7.78/1.50  --prep_sem_filter                       exhaustive
% 7.78/1.50  --prep_sem_filter_out                   false
% 7.78/1.50  --pred_elim                             true
% 7.78/1.50  --res_sim_input                         true
% 7.78/1.50  --eq_ax_congr_red                       true
% 7.78/1.50  --pure_diseq_elim                       true
% 7.78/1.50  --brand_transform                       false
% 7.78/1.50  --non_eq_to_eq                          false
% 7.78/1.50  --prep_def_merge                        true
% 7.78/1.50  --prep_def_merge_prop_impl              false
% 7.78/1.50  --prep_def_merge_mbd                    true
% 7.78/1.50  --prep_def_merge_tr_red                 false
% 7.78/1.50  --prep_def_merge_tr_cl                  false
% 7.78/1.50  --smt_preprocessing                     true
% 7.78/1.50  --smt_ac_axioms                         fast
% 7.78/1.50  --preprocessed_out                      false
% 7.78/1.50  --preprocessed_stats                    false
% 7.78/1.50  
% 7.78/1.50  ------ Abstraction refinement Options
% 7.78/1.50  
% 7.78/1.50  --abstr_ref                             []
% 7.78/1.50  --abstr_ref_prep                        false
% 7.78/1.50  --abstr_ref_until_sat                   false
% 7.78/1.50  --abstr_ref_sig_restrict                funpre
% 7.78/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.50  --abstr_ref_under                       []
% 7.78/1.50  
% 7.78/1.50  ------ SAT Options
% 7.78/1.50  
% 7.78/1.50  --sat_mode                              false
% 7.78/1.50  --sat_fm_restart_options                ""
% 7.78/1.50  --sat_gr_def                            false
% 7.78/1.50  --sat_epr_types                         true
% 7.78/1.50  --sat_non_cyclic_types                  false
% 7.78/1.50  --sat_finite_models                     false
% 7.78/1.50  --sat_fm_lemmas                         false
% 7.78/1.50  --sat_fm_prep                           false
% 7.78/1.50  --sat_fm_uc_incr                        true
% 7.78/1.50  --sat_out_model                         small
% 7.78/1.50  --sat_out_clauses                       false
% 7.78/1.50  
% 7.78/1.50  ------ QBF Options
% 7.78/1.50  
% 7.78/1.50  --qbf_mode                              false
% 7.78/1.50  --qbf_elim_univ                         false
% 7.78/1.50  --qbf_dom_inst                          none
% 7.78/1.50  --qbf_dom_pre_inst                      false
% 7.78/1.50  --qbf_sk_in                             false
% 7.78/1.50  --qbf_pred_elim                         true
% 7.78/1.50  --qbf_split                             512
% 7.78/1.50  
% 7.78/1.50  ------ BMC1 Options
% 7.78/1.50  
% 7.78/1.50  --bmc1_incremental                      false
% 7.78/1.50  --bmc1_axioms                           reachable_all
% 7.78/1.50  --bmc1_min_bound                        0
% 7.78/1.50  --bmc1_max_bound                        -1
% 7.78/1.50  --bmc1_max_bound_default                -1
% 7.78/1.50  --bmc1_symbol_reachability              true
% 7.78/1.50  --bmc1_property_lemmas                  false
% 7.78/1.50  --bmc1_k_induction                      false
% 7.78/1.50  --bmc1_non_equiv_states                 false
% 7.78/1.50  --bmc1_deadlock                         false
% 7.78/1.50  --bmc1_ucm                              false
% 7.78/1.50  --bmc1_add_unsat_core                   none
% 7.78/1.50  --bmc1_unsat_core_children              false
% 7.78/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.50  --bmc1_out_stat                         full
% 7.78/1.50  --bmc1_ground_init                      false
% 7.78/1.50  --bmc1_pre_inst_next_state              false
% 7.78/1.50  --bmc1_pre_inst_state                   false
% 7.78/1.50  --bmc1_pre_inst_reach_state             false
% 7.78/1.50  --bmc1_out_unsat_core                   false
% 7.78/1.50  --bmc1_aig_witness_out                  false
% 7.78/1.50  --bmc1_verbose                          false
% 7.78/1.50  --bmc1_dump_clauses_tptp                false
% 7.78/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.50  --bmc1_dump_file                        -
% 7.78/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.50  --bmc1_ucm_extend_mode                  1
% 7.78/1.50  --bmc1_ucm_init_mode                    2
% 7.78/1.50  --bmc1_ucm_cone_mode                    none
% 7.78/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.50  --bmc1_ucm_relax_model                  4
% 7.78/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.50  --bmc1_ucm_layered_model                none
% 7.78/1.50  --bmc1_ucm_max_lemma_size               10
% 7.78/1.50  
% 7.78/1.50  ------ AIG Options
% 7.78/1.50  
% 7.78/1.50  --aig_mode                              false
% 7.78/1.50  
% 7.78/1.50  ------ Instantiation Options
% 7.78/1.50  
% 7.78/1.50  --instantiation_flag                    true
% 7.78/1.50  --inst_sos_flag                         false
% 7.78/1.50  --inst_sos_phase                        true
% 7.78/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.50  --inst_lit_sel_side                     num_symb
% 7.78/1.50  --inst_solver_per_active                1400
% 7.78/1.50  --inst_solver_calls_frac                1.
% 7.78/1.50  --inst_passive_queue_type               priority_queues
% 7.78/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.50  --inst_passive_queues_freq              [25;2]
% 7.78/1.50  --inst_dismatching                      true
% 7.78/1.50  --inst_eager_unprocessed_to_passive     true
% 7.78/1.50  --inst_prop_sim_given                   true
% 7.78/1.50  --inst_prop_sim_new                     false
% 7.78/1.50  --inst_subs_new                         false
% 7.78/1.50  --inst_eq_res_simp                      false
% 7.78/1.50  --inst_subs_given                       false
% 7.78/1.50  --inst_orphan_elimination               true
% 7.78/1.50  --inst_learning_loop_flag               true
% 7.78/1.50  --inst_learning_start                   3000
% 7.78/1.50  --inst_learning_factor                  2
% 7.78/1.50  --inst_start_prop_sim_after_learn       3
% 7.78/1.50  --inst_sel_renew                        solver
% 7.78/1.50  --inst_lit_activity_flag                true
% 7.78/1.50  --inst_restr_to_given                   false
% 7.78/1.50  --inst_activity_threshold               500
% 7.78/1.50  --inst_out_proof                        true
% 7.78/1.50  
% 7.78/1.50  ------ Resolution Options
% 7.78/1.50  
% 7.78/1.50  --resolution_flag                       true
% 7.78/1.50  --res_lit_sel                           adaptive
% 7.78/1.50  --res_lit_sel_side                      none
% 7.78/1.50  --res_ordering                          kbo
% 7.78/1.50  --res_to_prop_solver                    active
% 7.78/1.50  --res_prop_simpl_new                    false
% 7.78/1.50  --res_prop_simpl_given                  true
% 7.78/1.50  --res_passive_queue_type                priority_queues
% 7.78/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.50  --res_passive_queues_freq               [15;5]
% 7.78/1.50  --res_forward_subs                      full
% 7.78/1.50  --res_backward_subs                     full
% 7.78/1.50  --res_forward_subs_resolution           true
% 7.78/1.50  --res_backward_subs_resolution          true
% 7.78/1.50  --res_orphan_elimination                true
% 7.78/1.50  --res_time_limit                        2.
% 7.78/1.50  --res_out_proof                         true
% 7.78/1.50  
% 7.78/1.50  ------ Superposition Options
% 7.78/1.50  
% 7.78/1.50  --superposition_flag                    true
% 7.78/1.50  --sup_passive_queue_type                priority_queues
% 7.78/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.50  --demod_completeness_check              fast
% 7.78/1.50  --demod_use_ground                      true
% 7.78/1.50  --sup_to_prop_solver                    passive
% 7.78/1.50  --sup_prop_simpl_new                    true
% 7.78/1.50  --sup_prop_simpl_given                  true
% 7.78/1.50  --sup_fun_splitting                     false
% 7.78/1.50  --sup_smt_interval                      50000
% 7.78/1.50  
% 7.78/1.50  ------ Superposition Simplification Setup
% 7.78/1.50  
% 7.78/1.50  --sup_indices_passive                   []
% 7.78/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.78/1.50  --sup_full_bw                           [BwDemod]
% 7.78/1.50  --sup_immed_triv                        [TrivRules]
% 7.78/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.78/1.50  --sup_immed_bw_main                     []
% 7.78/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.78/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.78/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.78/1.50  
% 7.78/1.50  ------ Combination Options
% 7.78/1.50  
% 7.78/1.50  --comb_res_mult                         3
% 7.78/1.50  --comb_sup_mult                         2
% 7.78/1.50  --comb_inst_mult                        10
% 7.78/1.50  
% 7.78/1.50  ------ Debug Options
% 7.78/1.50  
% 7.78/1.50  --dbg_backtrace                         false
% 7.78/1.50  --dbg_dump_prop_clauses                 false
% 7.78/1.50  --dbg_dump_prop_clauses_file            -
% 7.78/1.50  --dbg_out_stat                          false
% 7.78/1.50  ------ Parsing...
% 7.78/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.78/1.50  
% 7.78/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.78/1.50  
% 7.78/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.78/1.50  
% 7.78/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.78/1.50  ------ Proving...
% 7.78/1.50  ------ Problem Properties 
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  clauses                                 13
% 7.78/1.50  conjectures                             4
% 7.78/1.50  EPR                                     1
% 7.78/1.50  Horn                                    13
% 7.78/1.50  unary                                   4
% 7.78/1.50  binary                                  4
% 7.78/1.50  lits                                    29
% 7.78/1.50  lits eq                                 5
% 7.78/1.50  fd_pure                                 0
% 7.78/1.50  fd_pseudo                               0
% 7.78/1.50  fd_cond                                 0
% 7.78/1.50  fd_pseudo_cond                          0
% 7.78/1.50  AC symbols                              0
% 7.78/1.50  
% 7.78/1.50  ------ Schedule dynamic 5 is on 
% 7.78/1.50  
% 7.78/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  ------ 
% 7.78/1.50  Current options:
% 7.78/1.50  ------ 
% 7.78/1.50  
% 7.78/1.50  ------ Input Options
% 7.78/1.50  
% 7.78/1.50  --out_options                           all
% 7.78/1.50  --tptp_safe_out                         true
% 7.78/1.50  --problem_path                          ""
% 7.78/1.50  --include_path                          ""
% 7.78/1.50  --clausifier                            res/vclausify_rel
% 7.78/1.50  --clausifier_options                    --mode clausify
% 7.78/1.50  --stdin                                 false
% 7.78/1.50  --stats_out                             all
% 7.78/1.50  
% 7.78/1.50  ------ General Options
% 7.78/1.50  
% 7.78/1.50  --fof                                   false
% 7.78/1.50  --time_out_real                         305.
% 7.78/1.50  --time_out_virtual                      -1.
% 7.78/1.50  --symbol_type_check                     false
% 7.78/1.50  --clausify_out                          false
% 7.78/1.50  --sig_cnt_out                           false
% 7.78/1.50  --trig_cnt_out                          false
% 7.78/1.50  --trig_cnt_out_tolerance                1.
% 7.78/1.50  --trig_cnt_out_sk_spl                   false
% 7.78/1.50  --abstr_cl_out                          false
% 7.78/1.50  
% 7.78/1.50  ------ Global Options
% 7.78/1.50  
% 7.78/1.50  --schedule                              default
% 7.78/1.50  --add_important_lit                     false
% 7.78/1.50  --prop_solver_per_cl                    1000
% 7.78/1.50  --min_unsat_core                        false
% 7.78/1.50  --soft_assumptions                      false
% 7.78/1.50  --soft_lemma_size                       3
% 7.78/1.50  --prop_impl_unit_size                   0
% 7.78/1.50  --prop_impl_unit                        []
% 7.78/1.50  --share_sel_clauses                     true
% 7.78/1.50  --reset_solvers                         false
% 7.78/1.50  --bc_imp_inh                            [conj_cone]
% 7.78/1.50  --conj_cone_tolerance                   3.
% 7.78/1.50  --extra_neg_conj                        none
% 7.78/1.50  --large_theory_mode                     true
% 7.78/1.50  --prolific_symb_bound                   200
% 7.78/1.50  --lt_threshold                          2000
% 7.78/1.50  --clause_weak_htbl                      true
% 7.78/1.50  --gc_record_bc_elim                     false
% 7.78/1.50  
% 7.78/1.50  ------ Preprocessing Options
% 7.78/1.50  
% 7.78/1.50  --preprocessing_flag                    true
% 7.78/1.50  --time_out_prep_mult                    0.1
% 7.78/1.50  --splitting_mode                        input
% 7.78/1.50  --splitting_grd                         true
% 7.78/1.50  --splitting_cvd                         false
% 7.78/1.50  --splitting_cvd_svl                     false
% 7.78/1.50  --splitting_nvd                         32
% 7.78/1.50  --sub_typing                            true
% 7.78/1.50  --prep_gs_sim                           true
% 7.78/1.50  --prep_unflatten                        true
% 7.78/1.50  --prep_res_sim                          true
% 7.78/1.50  --prep_upred                            true
% 7.78/1.50  --prep_sem_filter                       exhaustive
% 7.78/1.50  --prep_sem_filter_out                   false
% 7.78/1.50  --pred_elim                             true
% 7.78/1.50  --res_sim_input                         true
% 7.78/1.50  --eq_ax_congr_red                       true
% 7.78/1.50  --pure_diseq_elim                       true
% 7.78/1.50  --brand_transform                       false
% 7.78/1.50  --non_eq_to_eq                          false
% 7.78/1.50  --prep_def_merge                        true
% 7.78/1.50  --prep_def_merge_prop_impl              false
% 7.78/1.50  --prep_def_merge_mbd                    true
% 7.78/1.50  --prep_def_merge_tr_red                 false
% 7.78/1.50  --prep_def_merge_tr_cl                  false
% 7.78/1.50  --smt_preprocessing                     true
% 7.78/1.50  --smt_ac_axioms                         fast
% 7.78/1.50  --preprocessed_out                      false
% 7.78/1.50  --preprocessed_stats                    false
% 7.78/1.50  
% 7.78/1.50  ------ Abstraction refinement Options
% 7.78/1.50  
% 7.78/1.50  --abstr_ref                             []
% 7.78/1.50  --abstr_ref_prep                        false
% 7.78/1.50  --abstr_ref_until_sat                   false
% 7.78/1.50  --abstr_ref_sig_restrict                funpre
% 7.78/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.78/1.50  --abstr_ref_under                       []
% 7.78/1.50  
% 7.78/1.50  ------ SAT Options
% 7.78/1.50  
% 7.78/1.50  --sat_mode                              false
% 7.78/1.50  --sat_fm_restart_options                ""
% 7.78/1.50  --sat_gr_def                            false
% 7.78/1.50  --sat_epr_types                         true
% 7.78/1.50  --sat_non_cyclic_types                  false
% 7.78/1.50  --sat_finite_models                     false
% 7.78/1.50  --sat_fm_lemmas                         false
% 7.78/1.50  --sat_fm_prep                           false
% 7.78/1.50  --sat_fm_uc_incr                        true
% 7.78/1.50  --sat_out_model                         small
% 7.78/1.50  --sat_out_clauses                       false
% 7.78/1.50  
% 7.78/1.50  ------ QBF Options
% 7.78/1.50  
% 7.78/1.50  --qbf_mode                              false
% 7.78/1.50  --qbf_elim_univ                         false
% 7.78/1.50  --qbf_dom_inst                          none
% 7.78/1.50  --qbf_dom_pre_inst                      false
% 7.78/1.50  --qbf_sk_in                             false
% 7.78/1.50  --qbf_pred_elim                         true
% 7.78/1.50  --qbf_split                             512
% 7.78/1.50  
% 7.78/1.50  ------ BMC1 Options
% 7.78/1.50  
% 7.78/1.50  --bmc1_incremental                      false
% 7.78/1.50  --bmc1_axioms                           reachable_all
% 7.78/1.50  --bmc1_min_bound                        0
% 7.78/1.50  --bmc1_max_bound                        -1
% 7.78/1.50  --bmc1_max_bound_default                -1
% 7.78/1.50  --bmc1_symbol_reachability              true
% 7.78/1.50  --bmc1_property_lemmas                  false
% 7.78/1.50  --bmc1_k_induction                      false
% 7.78/1.50  --bmc1_non_equiv_states                 false
% 7.78/1.50  --bmc1_deadlock                         false
% 7.78/1.50  --bmc1_ucm                              false
% 7.78/1.50  --bmc1_add_unsat_core                   none
% 7.78/1.50  --bmc1_unsat_core_children              false
% 7.78/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.78/1.50  --bmc1_out_stat                         full
% 7.78/1.50  --bmc1_ground_init                      false
% 7.78/1.50  --bmc1_pre_inst_next_state              false
% 7.78/1.50  --bmc1_pre_inst_state                   false
% 7.78/1.50  --bmc1_pre_inst_reach_state             false
% 7.78/1.50  --bmc1_out_unsat_core                   false
% 7.78/1.50  --bmc1_aig_witness_out                  false
% 7.78/1.50  --bmc1_verbose                          false
% 7.78/1.50  --bmc1_dump_clauses_tptp                false
% 7.78/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.78/1.50  --bmc1_dump_file                        -
% 7.78/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.78/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.78/1.50  --bmc1_ucm_extend_mode                  1
% 7.78/1.50  --bmc1_ucm_init_mode                    2
% 7.78/1.50  --bmc1_ucm_cone_mode                    none
% 7.78/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.78/1.50  --bmc1_ucm_relax_model                  4
% 7.78/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.78/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.78/1.50  --bmc1_ucm_layered_model                none
% 7.78/1.50  --bmc1_ucm_max_lemma_size               10
% 7.78/1.50  
% 7.78/1.50  ------ AIG Options
% 7.78/1.50  
% 7.78/1.50  --aig_mode                              false
% 7.78/1.50  
% 7.78/1.50  ------ Instantiation Options
% 7.78/1.50  
% 7.78/1.50  --instantiation_flag                    true
% 7.78/1.50  --inst_sos_flag                         false
% 7.78/1.50  --inst_sos_phase                        true
% 7.78/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.78/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.78/1.50  --inst_lit_sel_side                     none
% 7.78/1.50  --inst_solver_per_active                1400
% 7.78/1.50  --inst_solver_calls_frac                1.
% 7.78/1.50  --inst_passive_queue_type               priority_queues
% 7.78/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.78/1.50  --inst_passive_queues_freq              [25;2]
% 7.78/1.50  --inst_dismatching                      true
% 7.78/1.50  --inst_eager_unprocessed_to_passive     true
% 7.78/1.50  --inst_prop_sim_given                   true
% 7.78/1.50  --inst_prop_sim_new                     false
% 7.78/1.50  --inst_subs_new                         false
% 7.78/1.50  --inst_eq_res_simp                      false
% 7.78/1.50  --inst_subs_given                       false
% 7.78/1.50  --inst_orphan_elimination               true
% 7.78/1.50  --inst_learning_loop_flag               true
% 7.78/1.50  --inst_learning_start                   3000
% 7.78/1.50  --inst_learning_factor                  2
% 7.78/1.50  --inst_start_prop_sim_after_learn       3
% 7.78/1.50  --inst_sel_renew                        solver
% 7.78/1.50  --inst_lit_activity_flag                true
% 7.78/1.50  --inst_restr_to_given                   false
% 7.78/1.50  --inst_activity_threshold               500
% 7.78/1.50  --inst_out_proof                        true
% 7.78/1.50  
% 7.78/1.50  ------ Resolution Options
% 7.78/1.50  
% 7.78/1.50  --resolution_flag                       false
% 7.78/1.50  --res_lit_sel                           adaptive
% 7.78/1.50  --res_lit_sel_side                      none
% 7.78/1.50  --res_ordering                          kbo
% 7.78/1.50  --res_to_prop_solver                    active
% 7.78/1.50  --res_prop_simpl_new                    false
% 7.78/1.50  --res_prop_simpl_given                  true
% 7.78/1.50  --res_passive_queue_type                priority_queues
% 7.78/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.78/1.50  --res_passive_queues_freq               [15;5]
% 7.78/1.50  --res_forward_subs                      full
% 7.78/1.50  --res_backward_subs                     full
% 7.78/1.50  --res_forward_subs_resolution           true
% 7.78/1.50  --res_backward_subs_resolution          true
% 7.78/1.50  --res_orphan_elimination                true
% 7.78/1.50  --res_time_limit                        2.
% 7.78/1.50  --res_out_proof                         true
% 7.78/1.50  
% 7.78/1.50  ------ Superposition Options
% 7.78/1.50  
% 7.78/1.50  --superposition_flag                    true
% 7.78/1.50  --sup_passive_queue_type                priority_queues
% 7.78/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.78/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.78/1.50  --demod_completeness_check              fast
% 7.78/1.50  --demod_use_ground                      true
% 7.78/1.50  --sup_to_prop_solver                    passive
% 7.78/1.50  --sup_prop_simpl_new                    true
% 7.78/1.50  --sup_prop_simpl_given                  true
% 7.78/1.50  --sup_fun_splitting                     false
% 7.78/1.50  --sup_smt_interval                      50000
% 7.78/1.50  
% 7.78/1.50  ------ Superposition Simplification Setup
% 7.78/1.50  
% 7.78/1.50  --sup_indices_passive                   []
% 7.78/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.78/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.78/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.78/1.50  --sup_full_bw                           [BwDemod]
% 7.78/1.50  --sup_immed_triv                        [TrivRules]
% 7.78/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.78/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.78/1.50  --sup_immed_bw_main                     []
% 7.78/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.78/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.78/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.78/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.78/1.50  
% 7.78/1.50  ------ Combination Options
% 7.78/1.50  
% 7.78/1.50  --comb_res_mult                         3
% 7.78/1.50  --comb_sup_mult                         2
% 7.78/1.50  --comb_inst_mult                        10
% 7.78/1.50  
% 7.78/1.50  ------ Debug Options
% 7.78/1.50  
% 7.78/1.50  --dbg_backtrace                         false
% 7.78/1.50  --dbg_dump_prop_clauses                 false
% 7.78/1.50  --dbg_dump_prop_clauses_file            -
% 7.78/1.50  --dbg_out_stat                          false
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  ------ Proving...
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  % SZS status Theorem for theBenchmark.p
% 7.78/1.50  
% 7.78/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.78/1.50  
% 7.78/1.50  fof(f10,conjecture,(
% 7.78/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 7.78/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f11,negated_conjecture,(
% 7.78/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 7.78/1.50    inference(negated_conjecture,[],[f10])).
% 7.78/1.50  
% 7.78/1.50  fof(f23,plain,(
% 7.78/1.50    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 7.78/1.50    inference(ennf_transformation,[],[f11])).
% 7.78/1.50  
% 7.78/1.50  fof(f24,plain,(
% 7.78/1.50    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 7.78/1.50    inference(flattening,[],[f23])).
% 7.78/1.50  
% 7.78/1.50  fof(f27,plain,(
% 7.78/1.50    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0) & v1_tops_2(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 7.78/1.50    introduced(choice_axiom,[])).
% 7.78/1.50  
% 7.78/1.50  fof(f26,plain,(
% 7.78/1.50    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0) & v1_tops_2(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 7.78/1.50    introduced(choice_axiom,[])).
% 7.78/1.50  
% 7.78/1.50  fof(f25,plain,(
% 7.78/1.50    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 7.78/1.50    introduced(choice_axiom,[])).
% 7.78/1.50  
% 7.78/1.50  fof(f28,plain,(
% 7.78/1.50    ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 7.78/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 7.78/1.50  
% 7.78/1.50  fof(f39,plain,(
% 7.78/1.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 7.78/1.50    inference(cnf_transformation,[],[f28])).
% 7.78/1.50  
% 7.78/1.50  fof(f40,plain,(
% 7.78/1.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 7.78/1.50    inference(cnf_transformation,[],[f28])).
% 7.78/1.50  
% 7.78/1.50  fof(f3,axiom,(
% 7.78/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.78/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f15,plain,(
% 7.78/1.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.78/1.50    inference(ennf_transformation,[],[f3])).
% 7.78/1.50  
% 7.78/1.50  fof(f31,plain,(
% 7.78/1.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f15])).
% 7.78/1.50  
% 7.78/1.50  fof(f7,axiom,(
% 7.78/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))))),
% 7.78/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f19,plain,(
% 7.78/1.50    ! [X0,X1] : (! [X2] : (k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.78/1.50    inference(ennf_transformation,[],[f7])).
% 7.78/1.50  
% 7.78/1.50  fof(f35,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f19])).
% 7.78/1.50  
% 7.78/1.50  fof(f6,axiom,(
% 7.78/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 7.78/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f18,plain,(
% 7.78/1.50    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.78/1.50    inference(ennf_transformation,[],[f6])).
% 7.78/1.50  
% 7.78/1.50  fof(f34,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f18])).
% 7.78/1.50  
% 7.78/1.50  fof(f5,axiom,(
% 7.78/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.78/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f17,plain,(
% 7.78/1.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.78/1.50    inference(ennf_transformation,[],[f5])).
% 7.78/1.50  
% 7.78/1.50  fof(f33,plain,(
% 7.78/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f17])).
% 7.78/1.50  
% 7.78/1.50  fof(f8,axiom,(
% 7.78/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 7.78/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f20,plain,(
% 7.78/1.50    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.78/1.50    inference(ennf_transformation,[],[f8])).
% 7.78/1.50  
% 7.78/1.50  fof(f36,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f20])).
% 7.78/1.50  
% 7.78/1.50  fof(f2,axiom,(
% 7.78/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 7.78/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f14,plain,(
% 7.78/1.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.78/1.50    inference(ennf_transformation,[],[f2])).
% 7.78/1.50  
% 7.78/1.50  fof(f30,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f14])).
% 7.78/1.50  
% 7.78/1.50  fof(f4,axiom,(
% 7.78/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.78/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f16,plain,(
% 7.78/1.50    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.78/1.50    inference(ennf_transformation,[],[f4])).
% 7.78/1.50  
% 7.78/1.50  fof(f32,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.78/1.50    inference(cnf_transformation,[],[f16])).
% 7.78/1.50  
% 7.78/1.50  fof(f9,axiom,(
% 7.78/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 7.78/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.78/1.50  
% 7.78/1.50  fof(f21,plain,(
% 7.78/1.50    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.78/1.50    inference(ennf_transformation,[],[f9])).
% 7.78/1.50  
% 7.78/1.50  fof(f22,plain,(
% 7.78/1.50    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.78/1.50    inference(flattening,[],[f21])).
% 7.78/1.50  
% 7.78/1.50  fof(f37,plain,(
% 7.78/1.50    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.78/1.50    inference(cnf_transformation,[],[f22])).
% 7.78/1.50  
% 7.78/1.50  fof(f38,plain,(
% 7.78/1.50    l1_pre_topc(sK0)),
% 7.78/1.50    inference(cnf_transformation,[],[f28])).
% 7.78/1.50  
% 7.78/1.50  fof(f42,plain,(
% 7.78/1.50    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 7.78/1.50    inference(cnf_transformation,[],[f28])).
% 7.78/1.50  
% 7.78/1.50  fof(f41,plain,(
% 7.78/1.50    v1_tops_2(sK1,sK0)),
% 7.78/1.50    inference(cnf_transformation,[],[f28])).
% 7.78/1.50  
% 7.78/1.50  cnf(c_12,negated_conjecture,
% 7.78/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_335,negated_conjecture,
% 7.78/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_620,plain,
% 7.78/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_11,negated_conjecture,
% 7.78/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_336,negated_conjecture,
% 7.78/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_619,plain,
% 7.78/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_2,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.78/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_344,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 7.78/1.50      | m1_subset_1(k3_subset_1(X0_43,X0_41),k1_zfmisc_1(X0_43)) ),
% 7.78/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_611,plain,
% 7.78/1.50      ( m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
% 7.78/1.50      | m1_subset_1(k3_subset_1(X0_43,X0_41),k1_zfmisc_1(X0_43)) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_6,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.78/1.50      | k3_subset_1(X1,k7_subset_1(X1,X2,X0)) = k4_subset_1(X1,k3_subset_1(X1,X2),X0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_340,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 7.78/1.50      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
% 7.78/1.50      | k3_subset_1(X0_43,k7_subset_1(X0_43,X0_41,X1_41)) = k4_subset_1(X0_43,k3_subset_1(X0_43,X0_41),X1_41) ),
% 7.78/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_615,plain,
% 7.78/1.50      ( k3_subset_1(X0_43,k7_subset_1(X0_43,X0_41,X1_41)) = k4_subset_1(X0_43,k3_subset_1(X0_43,X0_41),X1_41)
% 7.78/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1826,plain,
% 7.78/1.50      ( k3_subset_1(X0_43,k7_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41))) = k4_subset_1(X0_43,k3_subset_1(X0_43,X0_41),k3_subset_1(X0_43,X1_41))
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
% 7.78/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_611,c_615]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_29072,plain,
% 7.78/1.50      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_619,c_1826]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_30702,plain,
% 7.78/1.50      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) = k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_620,c_29072]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_5,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.78/1.50      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_341,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 7.78/1.50      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
% 7.78/1.50      | k9_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41)) = k7_subset_1(X0_43,X0_41,X1_41) ),
% 7.78/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_614,plain,
% 7.78/1.50      ( k9_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41)) = k7_subset_1(X0_43,X0_41,X1_41)
% 7.78/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1315,plain,
% 7.78/1.50      ( k9_subset_1(X0_43,X0_41,k3_subset_1(X0_43,k3_subset_1(X0_43,X1_41))) = k7_subset_1(X0_43,X0_41,k3_subset_1(X0_43,X1_41))
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
% 7.78/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_611,c_614]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_13582,plain,
% 7.78/1.50      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))) = k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2))
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_619,c_1315]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_4,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.78/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_342,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 7.78/1.50      | k3_subset_1(X0_43,k3_subset_1(X0_43,X0_41)) = X0_41 ),
% 7.78/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_613,plain,
% 7.78/1.50      ( k3_subset_1(X0_43,k3_subset_1(X0_43,X0_41)) = X0_41
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1019,plain,
% 7.78/1.50      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = sK2 ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_619,c_613]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_13653,plain,
% 7.78/1.50      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2)
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(light_normalisation,[status(thm)],[c_13582,c_1019]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_25234,plain,
% 7.78/1.50      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_620,c_13653]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_30796,plain,
% 7.78/1.50      ( k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2)) = k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)) ),
% 7.78/1.50      inference(light_normalisation,[status(thm)],[c_30702,c_25234]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_7,plain,
% 7.78/1.50      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
% 7.78/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 7.78/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
% 7.78/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_339,plain,
% 7.78/1.50      ( r1_tarski(k3_subset_1(X0_43,k4_subset_1(X0_43,X0_41,X1_41)),k3_subset_1(X0_43,X0_41))
% 7.78/1.50      | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_43))
% 7.78/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) ),
% 7.78/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_616,plain,
% 7.78/1.50      ( r1_tarski(k3_subset_1(X0_43,k4_subset_1(X0_43,X0_41,X1_41)),k3_subset_1(X0_43,X0_41)) = iProver_top
% 7.78/1.50      | m1_subset_1(X1_41,k1_zfmisc_1(X0_43)) != iProver_top
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_31108,plain,
% 7.78/1.50      ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1))) = iProver_top
% 7.78/1.50      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.78/1.50      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_30796,c_616]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1020,plain,
% 7.78/1.50      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1)) = sK1 ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_620,c_613]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_31109,plain,
% 7.78/1.50      ( r1_tarski(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))),sK1) = iProver_top
% 7.78/1.50      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.78/1.50      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(light_normalisation,[status(thm)],[c_31108,c_1020]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.50      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_345,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 7.78/1.50      | k9_subset_1(X0_43,X0_41,X1_41) = k9_subset_1(X0_43,X1_41,X0_41) ),
% 7.78/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_610,plain,
% 7.78/1.50      ( k9_subset_1(X0_43,X0_41,X1_41) = k9_subset_1(X0_43,X1_41,X0_41)
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1187,plain,
% 7.78/1.50      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1) ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_620,c_610]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_3,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.78/1.50      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.78/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_343,plain,
% 7.78/1.50      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 7.78/1.50      | m1_subset_1(k9_subset_1(X0_43,X1_41,X0_41),k1_zfmisc_1(X0_43)) ),
% 7.78/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_612,plain,
% 7.78/1.50      ( m1_subset_1(X0_41,k1_zfmisc_1(X0_43)) != iProver_top
% 7.78/1.50      | m1_subset_1(k9_subset_1(X0_43,X1_41,X0_41),k1_zfmisc_1(X0_43)) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_1506,plain,
% 7.78/1.50      ( m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.78/1.50      | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_1187,c_612]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_15,plain,
% 7.78/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_731,plain,
% 7.78/1.50      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.78/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_343]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_732,plain,
% 7.78/1.50      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.78/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_5482,plain,
% 7.78/1.50      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 7.78/1.50      inference(global_propositional_subsumption,
% 7.78/1.50                [status(thm)],
% 7.78/1.50                [c_1506,c_15,c_732]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_5489,plain,
% 7.78/1.50      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_1187,c_5482]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_5905,plain,
% 7.78/1.50      ( k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41))) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41) ),
% 7.78/1.50      inference(superposition,[status(thm)],[c_5489,c_613]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_31110,plain,
% 7.78/1.50      ( r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) = iProver_top
% 7.78/1.50      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.78/1.50      | m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(demodulation,[status(thm)],[c_31109,c_5905]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_726,plain,
% 7.78/1.50      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.78/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_343]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_727,plain,
% 7.78/1.50      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.78/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_729,plain,
% 7.78/1.50      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.78/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_727]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_717,plain,
% 7.78/1.50      ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.78/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_344]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_718,plain,
% 7.78/1.50      ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.78/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_714,plain,
% 7.78/1.50      ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.78/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_344]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_715,plain,
% 7.78/1.50      ( m1_subset_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.78/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_8,plain,
% 7.78/1.50      ( ~ v1_tops_2(X0,X1)
% 7.78/1.50      | v1_tops_2(X2,X1)
% 7.78/1.50      | ~ r1_tarski(X2,X0)
% 7.78/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.78/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.78/1.50      | ~ l1_pre_topc(X1) ),
% 7.78/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_13,negated_conjecture,
% 7.78/1.50      ( l1_pre_topc(sK0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_158,plain,
% 7.78/1.50      ( ~ v1_tops_2(X0,X1)
% 7.78/1.50      | v1_tops_2(X2,X1)
% 7.78/1.50      | ~ r1_tarski(X2,X0)
% 7.78/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.78/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.78/1.50      | sK0 != X1 ),
% 7.78/1.50      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_159,plain,
% 7.78/1.50      ( ~ v1_tops_2(X0,sK0)
% 7.78/1.50      | v1_tops_2(X1,sK0)
% 7.78/1.50      | ~ r1_tarski(X1,X0)
% 7.78/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.78/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(unflattening,[status(thm)],[c_158]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_334,plain,
% 7.78/1.50      ( ~ v1_tops_2(X0_41,sK0)
% 7.78/1.50      | v1_tops_2(X1_41,sK0)
% 7.78/1.50      | ~ r1_tarski(X1_41,X0_41)
% 7.78/1.50      | ~ m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.78/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(subtyping,[status(esa)],[c_159]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_709,plain,
% 7.78/1.50      ( ~ v1_tops_2(X0_41,sK0)
% 7.78/1.50      | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
% 7.78/1.50      | ~ r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),X0_41)
% 7.78/1.50      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.78/1.50      | ~ m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_334]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_710,plain,
% 7.78/1.50      ( v1_tops_2(X0_41,sK0) != iProver_top
% 7.78/1.50      | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) = iProver_top
% 7.78/1.50      | r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),X0_41) != iProver_top
% 7.78/1.50      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.78/1.50      | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_712,plain,
% 7.78/1.50      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) = iProver_top
% 7.78/1.50      | v1_tops_2(sK1,sK0) != iProver_top
% 7.78/1.50      | r1_tarski(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK1) != iProver_top
% 7.78/1.50      | m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.78/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.78/1.50      inference(instantiation,[status(thm)],[c_710]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_9,negated_conjecture,
% 7.78/1.50      ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_18,plain,
% 7.78/1.50      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) != iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_10,negated_conjecture,
% 7.78/1.50      ( v1_tops_2(sK1,sK0) ),
% 7.78/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_17,plain,
% 7.78/1.50      ( v1_tops_2(sK1,sK0) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(c_16,plain,
% 7.78/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 7.78/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.78/1.50  
% 7.78/1.50  cnf(contradiction,plain,
% 7.78/1.50      ( $false ),
% 7.78/1.50      inference(minisat,
% 7.78/1.50                [status(thm)],
% 7.78/1.50                [c_31110,c_729,c_718,c_715,c_712,c_18,c_17,c_16,c_15]) ).
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.78/1.50  
% 7.78/1.50  ------                               Statistics
% 7.78/1.50  
% 7.78/1.50  ------ General
% 7.78/1.50  
% 7.78/1.50  abstr_ref_over_cycles:                  0
% 7.78/1.50  abstr_ref_under_cycles:                 0
% 7.78/1.50  gc_basic_clause_elim:                   0
% 7.78/1.50  forced_gc_time:                         0
% 7.78/1.50  parsing_time:                           0.006
% 7.78/1.50  unif_index_cands_time:                  0.
% 7.78/1.50  unif_index_add_time:                    0.
% 7.78/1.50  orderings_time:                         0.
% 7.78/1.50  out_proof_time:                         0.01
% 7.78/1.50  total_time:                             0.95
% 7.78/1.50  num_of_symbols:                         44
% 7.78/1.50  num_of_terms:                           33571
% 7.78/1.50  
% 7.78/1.50  ------ Preprocessing
% 7.78/1.50  
% 7.78/1.50  num_of_splits:                          0
% 7.78/1.50  num_of_split_atoms:                     0
% 7.78/1.50  num_of_reused_defs:                     0
% 7.78/1.50  num_eq_ax_congr_red:                    23
% 7.78/1.50  num_of_sem_filtered_clauses:            1
% 7.78/1.50  num_of_subtypes:                        3
% 7.78/1.50  monotx_restored_types:                  0
% 7.78/1.50  sat_num_of_epr_types:                   0
% 7.78/1.50  sat_num_of_non_cyclic_types:            0
% 7.78/1.50  sat_guarded_non_collapsed_types:        1
% 7.78/1.50  num_pure_diseq_elim:                    0
% 7.78/1.50  simp_replaced_by:                       0
% 7.78/1.50  res_preprocessed:                       70
% 7.78/1.50  prep_upred:                             0
% 7.78/1.50  prep_unflattend:                        5
% 7.78/1.50  smt_new_axioms:                         0
% 7.78/1.50  pred_elim_cands:                        3
% 7.78/1.50  pred_elim:                              1
% 7.78/1.50  pred_elim_cl:                           1
% 7.78/1.50  pred_elim_cycles:                       3
% 7.78/1.50  merged_defs:                            0
% 7.78/1.50  merged_defs_ncl:                        0
% 7.78/1.50  bin_hyper_res:                          0
% 7.78/1.50  prep_cycles:                            4
% 7.78/1.50  pred_elim_time:                         0.001
% 7.78/1.50  splitting_time:                         0.
% 7.78/1.50  sem_filter_time:                        0.
% 7.78/1.50  monotx_time:                            0.
% 7.78/1.50  subtype_inf_time:                       0.
% 7.78/1.50  
% 7.78/1.50  ------ Problem properties
% 7.78/1.50  
% 7.78/1.50  clauses:                                13
% 7.78/1.50  conjectures:                            4
% 7.78/1.50  epr:                                    1
% 7.78/1.50  horn:                                   13
% 7.78/1.50  ground:                                 4
% 7.78/1.50  unary:                                  4
% 7.78/1.50  binary:                                 4
% 7.78/1.50  lits:                                   29
% 7.78/1.50  lits_eq:                                5
% 7.78/1.50  fd_pure:                                0
% 7.78/1.50  fd_pseudo:                              0
% 7.78/1.50  fd_cond:                                0
% 7.78/1.50  fd_pseudo_cond:                         0
% 7.78/1.50  ac_symbols:                             0
% 7.78/1.50  
% 7.78/1.50  ------ Propositional Solver
% 7.78/1.50  
% 7.78/1.50  prop_solver_calls:                      30
% 7.78/1.50  prop_fast_solver_calls:                 680
% 7.78/1.50  smt_solver_calls:                       0
% 7.78/1.50  smt_fast_solver_calls:                  0
% 7.78/1.50  prop_num_of_clauses:                    9787
% 7.78/1.50  prop_preprocess_simplified:             12740
% 7.78/1.50  prop_fo_subsumed:                       5
% 7.78/1.50  prop_solver_time:                       0.
% 7.78/1.50  smt_solver_time:                        0.
% 7.78/1.50  smt_fast_solver_time:                   0.
% 7.78/1.50  prop_fast_solver_time:                  0.
% 7.78/1.50  prop_unsat_core_time:                   0.001
% 7.78/1.50  
% 7.78/1.50  ------ QBF
% 7.78/1.50  
% 7.78/1.50  qbf_q_res:                              0
% 7.78/1.50  qbf_num_tautologies:                    0
% 7.78/1.50  qbf_prep_cycles:                        0
% 7.78/1.50  
% 7.78/1.50  ------ BMC1
% 7.78/1.50  
% 7.78/1.50  bmc1_current_bound:                     -1
% 7.78/1.50  bmc1_last_solved_bound:                 -1
% 7.78/1.50  bmc1_unsat_core_size:                   -1
% 7.78/1.50  bmc1_unsat_core_parents_size:           -1
% 7.78/1.50  bmc1_merge_next_fun:                    0
% 7.78/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.78/1.50  
% 7.78/1.50  ------ Instantiation
% 7.78/1.50  
% 7.78/1.50  inst_num_of_clauses:                    2051
% 7.78/1.50  inst_num_in_passive:                    537
% 7.78/1.50  inst_num_in_active:                     983
% 7.78/1.50  inst_num_in_unprocessed:                531
% 7.78/1.50  inst_num_of_loops:                      1040
% 7.78/1.50  inst_num_of_learning_restarts:          0
% 7.78/1.50  inst_num_moves_active_passive:          53
% 7.78/1.50  inst_lit_activity:                      0
% 7.78/1.50  inst_lit_activity_moves:                0
% 7.78/1.50  inst_num_tautologies:                   0
% 7.78/1.50  inst_num_prop_implied:                  0
% 7.78/1.50  inst_num_existing_simplified:           0
% 7.78/1.50  inst_num_eq_res_simplified:             0
% 7.78/1.50  inst_num_child_elim:                    0
% 7.78/1.50  inst_num_of_dismatching_blockings:      2854
% 7.78/1.50  inst_num_of_non_proper_insts:           2454
% 7.78/1.50  inst_num_of_duplicates:                 0
% 7.78/1.50  inst_inst_num_from_inst_to_res:         0
% 7.78/1.50  inst_dismatching_checking_time:         0.
% 7.78/1.50  
% 7.78/1.50  ------ Resolution
% 7.78/1.50  
% 7.78/1.50  res_num_of_clauses:                     0
% 7.78/1.50  res_num_in_passive:                     0
% 7.78/1.50  res_num_in_active:                      0
% 7.78/1.50  res_num_of_loops:                       74
% 7.78/1.50  res_forward_subset_subsumed:            162
% 7.78/1.50  res_backward_subset_subsumed:           4
% 7.78/1.50  res_forward_subsumed:                   0
% 7.78/1.50  res_backward_subsumed:                  0
% 7.78/1.50  res_forward_subsumption_resolution:     0
% 7.78/1.50  res_backward_subsumption_resolution:    0
% 7.78/1.50  res_clause_to_clause_subsumption:       11199
% 7.78/1.50  res_orphan_elimination:                 0
% 7.78/1.50  res_tautology_del:                      500
% 7.78/1.50  res_num_eq_res_simplified:              0
% 7.78/1.50  res_num_sel_changes:                    0
% 7.78/1.50  res_moves_from_active_to_pass:          0
% 7.78/1.50  
% 7.78/1.50  ------ Superposition
% 7.78/1.50  
% 7.78/1.50  sup_time_total:                         0.
% 7.78/1.50  sup_time_generating:                    0.
% 7.78/1.50  sup_time_sim_full:                      0.
% 7.78/1.50  sup_time_sim_immed:                     0.
% 7.78/1.50  
% 7.78/1.50  sup_num_of_clauses:                     2103
% 7.78/1.50  sup_num_in_active:                      207
% 7.78/1.50  sup_num_in_passive:                     1896
% 7.78/1.50  sup_num_of_loops:                       206
% 7.78/1.50  sup_fw_superposition:                   2504
% 7.78/1.50  sup_bw_superposition:                   2201
% 7.78/1.50  sup_immediate_simplified:               1283
% 7.78/1.50  sup_given_eliminated:                   0
% 7.78/1.50  comparisons_done:                       0
% 7.78/1.50  comparisons_avoided:                    0
% 7.78/1.50  
% 7.78/1.50  ------ Simplifications
% 7.78/1.50  
% 7.78/1.50  
% 7.78/1.50  sim_fw_subset_subsumed:                 125
% 7.78/1.50  sim_bw_subset_subsumed:                 79
% 7.78/1.50  sim_fw_subsumed:                        395
% 7.78/1.50  sim_bw_subsumed:                        95
% 7.78/1.50  sim_fw_subsumption_res:                 0
% 7.78/1.50  sim_bw_subsumption_res:                 0
% 7.78/1.50  sim_tautology_del:                      2
% 7.78/1.50  sim_eq_tautology_del:                   114
% 7.78/1.50  sim_eq_res_simp:                        0
% 7.78/1.50  sim_fw_demodulated:                     184
% 7.78/1.50  sim_bw_demodulated:                     53
% 7.78/1.50  sim_light_normalised:                   501
% 7.78/1.50  sim_joinable_taut:                      0
% 7.78/1.50  sim_joinable_simp:                      0
% 7.78/1.50  sim_ac_normalised:                      0
% 7.78/1.50  sim_smt_subsumption:                    0
% 7.78/1.50  
%------------------------------------------------------------------------------
