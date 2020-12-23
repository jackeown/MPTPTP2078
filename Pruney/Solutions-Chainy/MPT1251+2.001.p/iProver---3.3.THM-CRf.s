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
% DateTime   : Thu Dec  3 12:14:06 EST 2020

% Result     : Theorem 15.20s
% Output     : CNFRefutation 15.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 526 expanded)
%              Number of clauses        :   78 ( 191 expanded)
%              Number of leaves         :   13 ( 139 expanded)
%              Depth                    :   21
%              Number of atoms          :  280 (1848 expanded)
%              Number of equality atoms :  106 ( 229 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,sK1),k2_tops_1(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k2_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_346,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_582,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_345,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_583,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k3_subset_1(X1_44,X0_44) = k4_xboole_0(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_575,plain,
    ( k3_subset_1(X0_44,X1_44) = k4_xboole_0(X0_44,X1_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_895,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_583,c_575])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_352,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_576,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_1101,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_895,c_576])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1302,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1101,c_16])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
    | k9_subset_1(X1_44,X0_44,k3_subset_1(X1_44,X2_44)) = k7_subset_1(X1_44,X0_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_580,plain,
    ( k9_subset_1(X0_44,X1_44,k3_subset_1(X0_44,X2_44)) = k7_subset_1(X0_44,X1_44,X2_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_1779,plain,
    ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),X0_44)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1302,c_580])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k7_subset_1(X1_44,X0_44,X2_44) = k4_xboole_0(X0_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_579,plain,
    ( k7_subset_1(X0_44,X1_44,X2_44) = k4_xboole_0(X1_44,X2_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_1307,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_44) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0_44) ),
    inference(superposition,[status(thm)],[c_1302,c_579])).

cnf(c_0,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_354,plain,
    ( k4_xboole_0(k4_xboole_0(X0_44,X1_44),X2_44) = k4_xboole_0(X0_44,k2_xboole_0(X1_44,X2_44)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1309,plain,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_44) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,X0_44)) ),
    inference(demodulation,[status(thm)],[c_1307,c_354])).

cnf(c_1780,plain,
    ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),X0_44)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,X0_44))
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1779,c_1309])).

cnf(c_39860,plain,
    ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_582,c_1780])).

cnf(c_894,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_582,c_575])).

cnf(c_39905,plain,
    ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_39860,c_894])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_206,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_207,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0_44)) = k2_tops_1(sK0,X0_44) ),
    inference(subtyping,[status(esa)],[c_207])).

cnf(c_585,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0_44)) = k2_tops_1(sK0,X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_699,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k2_tops_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_582,c_585])).

cnf(c_700,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_583,c_585])).

cnf(c_8,plain,
    ( r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_181,plain,
    ( r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_182,plain,
    ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_182,c_12])).

cnf(c_187,plain,
    ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_186])).

cnf(c_344,plain,
    ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0_44,X1_44)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_44),k2_tops_1(sK0,X1_44)))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_187])).

cnf(c_584,plain,
    ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0_44,X1_44)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_44),k2_tops_1(sK0,X1_44))) = iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_830,plain,
    ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0_44)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,X0_44))) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_584])).

cnf(c_848,plain,
    ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_830])).

cnf(c_1027,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_44),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_1028,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_44),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1027])).

cnf(c_1030,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_6376,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_848,c_16,c_1030])).

cnf(c_6377,plain,
    ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6376])).

cnf(c_6380,plain,
    ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top
    | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6377,c_894,c_895])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1042,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_894,c_576])).

cnf(c_6382,plain,
    ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6380,c_17,c_1042])).

cnf(c_41309,plain,
    ( r1_tarski(k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_39905,c_6382])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
    | k4_subset_1(X1_44,X0_44,X2_44) = k2_xboole_0(X0_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_578,plain,
    ( k4_subset_1(X0_44,X1_44,X2_44) = k2_xboole_0(X1_44,X2_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_1419,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0_44) = k2_xboole_0(sK1,X0_44)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_578])).

cnf(c_1558,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_582,c_1419])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(k4_subset_1(X1_44,X0_44,X2_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_577,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(X2_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(k4_subset_1(X1_44,X0_44,X2_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_1622,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_577])).

cnf(c_4212,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1622,c_16,c_17])).

cnf(c_4223,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4212,c_585])).

cnf(c_4229,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4212,c_575])).

cnf(c_4234,plain,
    ( k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_4223,c_4229])).

cnf(c_41310,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41309,c_4234])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_347,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_581,plain,
    ( r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_1620,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1558,c_581])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41310,c_1620])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:17:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.20/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.20/2.48  
% 15.20/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.20/2.48  
% 15.20/2.48  ------  iProver source info
% 15.20/2.48  
% 15.20/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.20/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.20/2.48  git: non_committed_changes: false
% 15.20/2.48  git: last_make_outside_of_git: false
% 15.20/2.48  
% 15.20/2.48  ------ 
% 15.20/2.48  
% 15.20/2.48  ------ Input Options
% 15.20/2.48  
% 15.20/2.48  --out_options                           all
% 15.20/2.48  --tptp_safe_out                         true
% 15.20/2.48  --problem_path                          ""
% 15.20/2.48  --include_path                          ""
% 15.20/2.48  --clausifier                            res/vclausify_rel
% 15.20/2.48  --clausifier_options                    ""
% 15.20/2.48  --stdin                                 false
% 15.20/2.48  --stats_out                             all
% 15.20/2.48  
% 15.20/2.48  ------ General Options
% 15.20/2.48  
% 15.20/2.48  --fof                                   false
% 15.20/2.48  --time_out_real                         305.
% 15.20/2.48  --time_out_virtual                      -1.
% 15.20/2.48  --symbol_type_check                     false
% 15.20/2.48  --clausify_out                          false
% 15.20/2.48  --sig_cnt_out                           false
% 15.20/2.48  --trig_cnt_out                          false
% 15.20/2.48  --trig_cnt_out_tolerance                1.
% 15.20/2.48  --trig_cnt_out_sk_spl                   false
% 15.20/2.48  --abstr_cl_out                          false
% 15.20/2.48  
% 15.20/2.48  ------ Global Options
% 15.20/2.48  
% 15.20/2.48  --schedule                              default
% 15.20/2.48  --add_important_lit                     false
% 15.20/2.48  --prop_solver_per_cl                    1000
% 15.20/2.48  --min_unsat_core                        false
% 15.20/2.48  --soft_assumptions                      false
% 15.20/2.48  --soft_lemma_size                       3
% 15.20/2.48  --prop_impl_unit_size                   0
% 15.20/2.48  --prop_impl_unit                        []
% 15.20/2.48  --share_sel_clauses                     true
% 15.20/2.48  --reset_solvers                         false
% 15.20/2.48  --bc_imp_inh                            [conj_cone]
% 15.20/2.48  --conj_cone_tolerance                   3.
% 15.20/2.48  --extra_neg_conj                        none
% 15.20/2.48  --large_theory_mode                     true
% 15.20/2.48  --prolific_symb_bound                   200
% 15.20/2.48  --lt_threshold                          2000
% 15.20/2.48  --clause_weak_htbl                      true
% 15.20/2.48  --gc_record_bc_elim                     false
% 15.20/2.48  
% 15.20/2.48  ------ Preprocessing Options
% 15.20/2.48  
% 15.20/2.48  --preprocessing_flag                    true
% 15.20/2.48  --time_out_prep_mult                    0.1
% 15.20/2.48  --splitting_mode                        input
% 15.20/2.48  --splitting_grd                         true
% 15.20/2.48  --splitting_cvd                         false
% 15.20/2.48  --splitting_cvd_svl                     false
% 15.20/2.48  --splitting_nvd                         32
% 15.20/2.48  --sub_typing                            true
% 15.20/2.48  --prep_gs_sim                           true
% 15.20/2.48  --prep_unflatten                        true
% 15.20/2.48  --prep_res_sim                          true
% 15.20/2.48  --prep_upred                            true
% 15.20/2.48  --prep_sem_filter                       exhaustive
% 15.20/2.48  --prep_sem_filter_out                   false
% 15.20/2.48  --pred_elim                             true
% 15.20/2.48  --res_sim_input                         true
% 15.20/2.48  --eq_ax_congr_red                       true
% 15.20/2.48  --pure_diseq_elim                       true
% 15.20/2.48  --brand_transform                       false
% 15.20/2.48  --non_eq_to_eq                          false
% 15.20/2.48  --prep_def_merge                        true
% 15.20/2.48  --prep_def_merge_prop_impl              false
% 15.20/2.48  --prep_def_merge_mbd                    true
% 15.20/2.48  --prep_def_merge_tr_red                 false
% 15.20/2.48  --prep_def_merge_tr_cl                  false
% 15.20/2.48  --smt_preprocessing                     true
% 15.20/2.48  --smt_ac_axioms                         fast
% 15.20/2.48  --preprocessed_out                      false
% 15.20/2.48  --preprocessed_stats                    false
% 15.20/2.48  
% 15.20/2.48  ------ Abstraction refinement Options
% 15.20/2.48  
% 15.20/2.48  --abstr_ref                             []
% 15.20/2.48  --abstr_ref_prep                        false
% 15.20/2.48  --abstr_ref_until_sat                   false
% 15.20/2.48  --abstr_ref_sig_restrict                funpre
% 15.20/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.20/2.48  --abstr_ref_under                       []
% 15.20/2.48  
% 15.20/2.48  ------ SAT Options
% 15.20/2.48  
% 15.20/2.48  --sat_mode                              false
% 15.20/2.48  --sat_fm_restart_options                ""
% 15.20/2.48  --sat_gr_def                            false
% 15.20/2.48  --sat_epr_types                         true
% 15.20/2.48  --sat_non_cyclic_types                  false
% 15.20/2.48  --sat_finite_models                     false
% 15.20/2.48  --sat_fm_lemmas                         false
% 15.20/2.48  --sat_fm_prep                           false
% 15.20/2.48  --sat_fm_uc_incr                        true
% 15.20/2.48  --sat_out_model                         small
% 15.20/2.48  --sat_out_clauses                       false
% 15.20/2.48  
% 15.20/2.48  ------ QBF Options
% 15.20/2.48  
% 15.20/2.48  --qbf_mode                              false
% 15.20/2.48  --qbf_elim_univ                         false
% 15.20/2.48  --qbf_dom_inst                          none
% 15.20/2.48  --qbf_dom_pre_inst                      false
% 15.20/2.48  --qbf_sk_in                             false
% 15.20/2.48  --qbf_pred_elim                         true
% 15.20/2.48  --qbf_split                             512
% 15.20/2.48  
% 15.20/2.48  ------ BMC1 Options
% 15.20/2.48  
% 15.20/2.48  --bmc1_incremental                      false
% 15.20/2.48  --bmc1_axioms                           reachable_all
% 15.20/2.48  --bmc1_min_bound                        0
% 15.20/2.48  --bmc1_max_bound                        -1
% 15.20/2.48  --bmc1_max_bound_default                -1
% 15.20/2.48  --bmc1_symbol_reachability              true
% 15.20/2.48  --bmc1_property_lemmas                  false
% 15.20/2.48  --bmc1_k_induction                      false
% 15.20/2.48  --bmc1_non_equiv_states                 false
% 15.20/2.48  --bmc1_deadlock                         false
% 15.20/2.48  --bmc1_ucm                              false
% 15.20/2.48  --bmc1_add_unsat_core                   none
% 15.20/2.48  --bmc1_unsat_core_children              false
% 15.20/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.20/2.48  --bmc1_out_stat                         full
% 15.20/2.48  --bmc1_ground_init                      false
% 15.20/2.48  --bmc1_pre_inst_next_state              false
% 15.20/2.48  --bmc1_pre_inst_state                   false
% 15.20/2.48  --bmc1_pre_inst_reach_state             false
% 15.20/2.48  --bmc1_out_unsat_core                   false
% 15.20/2.48  --bmc1_aig_witness_out                  false
% 15.20/2.48  --bmc1_verbose                          false
% 15.20/2.48  --bmc1_dump_clauses_tptp                false
% 15.20/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.20/2.48  --bmc1_dump_file                        -
% 15.20/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.20/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.20/2.48  --bmc1_ucm_extend_mode                  1
% 15.20/2.48  --bmc1_ucm_init_mode                    2
% 15.20/2.48  --bmc1_ucm_cone_mode                    none
% 15.20/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.20/2.48  --bmc1_ucm_relax_model                  4
% 15.20/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.20/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.20/2.48  --bmc1_ucm_layered_model                none
% 15.20/2.48  --bmc1_ucm_max_lemma_size               10
% 15.20/2.48  
% 15.20/2.48  ------ AIG Options
% 15.20/2.48  
% 15.20/2.48  --aig_mode                              false
% 15.20/2.48  
% 15.20/2.48  ------ Instantiation Options
% 15.20/2.48  
% 15.20/2.48  --instantiation_flag                    true
% 15.20/2.48  --inst_sos_flag                         true
% 15.20/2.48  --inst_sos_phase                        true
% 15.20/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.20/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.20/2.48  --inst_lit_sel_side                     num_symb
% 15.20/2.48  --inst_solver_per_active                1400
% 15.20/2.48  --inst_solver_calls_frac                1.
% 15.20/2.48  --inst_passive_queue_type               priority_queues
% 15.20/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.20/2.48  --inst_passive_queues_freq              [25;2]
% 15.20/2.48  --inst_dismatching                      true
% 15.20/2.48  --inst_eager_unprocessed_to_passive     true
% 15.20/2.48  --inst_prop_sim_given                   true
% 15.20/2.48  --inst_prop_sim_new                     false
% 15.20/2.48  --inst_subs_new                         false
% 15.20/2.48  --inst_eq_res_simp                      false
% 15.20/2.48  --inst_subs_given                       false
% 15.20/2.48  --inst_orphan_elimination               true
% 15.20/2.48  --inst_learning_loop_flag               true
% 15.20/2.48  --inst_learning_start                   3000
% 15.20/2.48  --inst_learning_factor                  2
% 15.20/2.48  --inst_start_prop_sim_after_learn       3
% 15.20/2.48  --inst_sel_renew                        solver
% 15.20/2.48  --inst_lit_activity_flag                true
% 15.20/2.48  --inst_restr_to_given                   false
% 15.20/2.48  --inst_activity_threshold               500
% 15.20/2.48  --inst_out_proof                        true
% 15.20/2.48  
% 15.20/2.48  ------ Resolution Options
% 15.20/2.48  
% 15.20/2.48  --resolution_flag                       true
% 15.20/2.48  --res_lit_sel                           adaptive
% 15.20/2.48  --res_lit_sel_side                      none
% 15.20/2.48  --res_ordering                          kbo
% 15.20/2.48  --res_to_prop_solver                    active
% 15.20/2.48  --res_prop_simpl_new                    false
% 15.20/2.48  --res_prop_simpl_given                  true
% 15.20/2.48  --res_passive_queue_type                priority_queues
% 15.20/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.20/2.48  --res_passive_queues_freq               [15;5]
% 15.20/2.48  --res_forward_subs                      full
% 15.20/2.48  --res_backward_subs                     full
% 15.20/2.48  --res_forward_subs_resolution           true
% 15.20/2.48  --res_backward_subs_resolution          true
% 15.20/2.48  --res_orphan_elimination                true
% 15.20/2.48  --res_time_limit                        2.
% 15.20/2.48  --res_out_proof                         true
% 15.20/2.48  
% 15.20/2.48  ------ Superposition Options
% 15.20/2.48  
% 15.20/2.48  --superposition_flag                    true
% 15.20/2.48  --sup_passive_queue_type                priority_queues
% 15.20/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.20/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.20/2.48  --demod_completeness_check              fast
% 15.20/2.48  --demod_use_ground                      true
% 15.20/2.48  --sup_to_prop_solver                    passive
% 15.20/2.48  --sup_prop_simpl_new                    true
% 15.20/2.48  --sup_prop_simpl_given                  true
% 15.20/2.48  --sup_fun_splitting                     true
% 15.20/2.48  --sup_smt_interval                      50000
% 15.20/2.48  
% 15.20/2.48  ------ Superposition Simplification Setup
% 15.20/2.48  
% 15.20/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.20/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.20/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.20/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.20/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.20/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.20/2.48  --sup_immed_triv                        [TrivRules]
% 15.20/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.20/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.20/2.48  --sup_immed_bw_main                     []
% 15.20/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.20/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.20/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.20/2.48  --sup_input_bw                          []
% 15.20/2.48  
% 15.20/2.48  ------ Combination Options
% 15.20/2.48  
% 15.20/2.48  --comb_res_mult                         3
% 15.20/2.48  --comb_sup_mult                         2
% 15.20/2.48  --comb_inst_mult                        10
% 15.20/2.48  
% 15.20/2.48  ------ Debug Options
% 15.20/2.48  
% 15.20/2.48  --dbg_backtrace                         false
% 15.20/2.48  --dbg_dump_prop_clauses                 false
% 15.20/2.48  --dbg_dump_prop_clauses_file            -
% 15.20/2.48  --dbg_out_stat                          false
% 15.20/2.48  ------ Parsing...
% 15.20/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.20/2.48  
% 15.20/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 15.20/2.48  
% 15.20/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.20/2.48  
% 15.20/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.20/2.48  ------ Proving...
% 15.20/2.48  ------ Problem Properties 
% 15.20/2.48  
% 15.20/2.48  
% 15.20/2.48  clauses                                 12
% 15.20/2.48  conjectures                             3
% 15.20/2.48  EPR                                     0
% 15.20/2.48  Horn                                    12
% 15.20/2.48  unary                                   4
% 15.20/2.48  binary                                  4
% 15.20/2.48  lits                                    24
% 15.20/2.48  lits eq                                 6
% 15.20/2.48  fd_pure                                 0
% 15.20/2.48  fd_pseudo                               0
% 15.20/2.48  fd_cond                                 0
% 15.20/2.48  fd_pseudo_cond                          0
% 15.20/2.48  AC symbols                              0
% 15.20/2.48  
% 15.20/2.48  ------ Schedule dynamic 5 is on 
% 15.20/2.48  
% 15.20/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.20/2.48  
% 15.20/2.48  
% 15.20/2.48  ------ 
% 15.20/2.48  Current options:
% 15.20/2.48  ------ 
% 15.20/2.48  
% 15.20/2.48  ------ Input Options
% 15.20/2.48  
% 15.20/2.48  --out_options                           all
% 15.20/2.48  --tptp_safe_out                         true
% 15.20/2.48  --problem_path                          ""
% 15.20/2.48  --include_path                          ""
% 15.20/2.48  --clausifier                            res/vclausify_rel
% 15.20/2.48  --clausifier_options                    ""
% 15.20/2.48  --stdin                                 false
% 15.20/2.48  --stats_out                             all
% 15.20/2.48  
% 15.20/2.48  ------ General Options
% 15.20/2.48  
% 15.20/2.48  --fof                                   false
% 15.20/2.48  --time_out_real                         305.
% 15.20/2.48  --time_out_virtual                      -1.
% 15.20/2.48  --symbol_type_check                     false
% 15.20/2.48  --clausify_out                          false
% 15.20/2.48  --sig_cnt_out                           false
% 15.20/2.48  --trig_cnt_out                          false
% 15.20/2.48  --trig_cnt_out_tolerance                1.
% 15.20/2.48  --trig_cnt_out_sk_spl                   false
% 15.20/2.48  --abstr_cl_out                          false
% 15.20/2.48  
% 15.20/2.48  ------ Global Options
% 15.20/2.48  
% 15.20/2.48  --schedule                              default
% 15.20/2.48  --add_important_lit                     false
% 15.20/2.48  --prop_solver_per_cl                    1000
% 15.20/2.48  --min_unsat_core                        false
% 15.20/2.48  --soft_assumptions                      false
% 15.20/2.48  --soft_lemma_size                       3
% 15.20/2.48  --prop_impl_unit_size                   0
% 15.20/2.48  --prop_impl_unit                        []
% 15.20/2.48  --share_sel_clauses                     true
% 15.20/2.48  --reset_solvers                         false
% 15.20/2.48  --bc_imp_inh                            [conj_cone]
% 15.20/2.48  --conj_cone_tolerance                   3.
% 15.20/2.48  --extra_neg_conj                        none
% 15.20/2.48  --large_theory_mode                     true
% 15.20/2.48  --prolific_symb_bound                   200
% 15.20/2.48  --lt_threshold                          2000
% 15.20/2.48  --clause_weak_htbl                      true
% 15.20/2.48  --gc_record_bc_elim                     false
% 15.20/2.48  
% 15.20/2.48  ------ Preprocessing Options
% 15.20/2.48  
% 15.20/2.48  --preprocessing_flag                    true
% 15.20/2.48  --time_out_prep_mult                    0.1
% 15.20/2.48  --splitting_mode                        input
% 15.20/2.48  --splitting_grd                         true
% 15.20/2.48  --splitting_cvd                         false
% 15.20/2.48  --splitting_cvd_svl                     false
% 15.20/2.48  --splitting_nvd                         32
% 15.20/2.48  --sub_typing                            true
% 15.20/2.48  --prep_gs_sim                           true
% 15.20/2.48  --prep_unflatten                        true
% 15.20/2.48  --prep_res_sim                          true
% 15.20/2.48  --prep_upred                            true
% 15.20/2.48  --prep_sem_filter                       exhaustive
% 15.20/2.48  --prep_sem_filter_out                   false
% 15.20/2.48  --pred_elim                             true
% 15.20/2.48  --res_sim_input                         true
% 15.20/2.48  --eq_ax_congr_red                       true
% 15.20/2.48  --pure_diseq_elim                       true
% 15.20/2.48  --brand_transform                       false
% 15.20/2.48  --non_eq_to_eq                          false
% 15.20/2.48  --prep_def_merge                        true
% 15.20/2.48  --prep_def_merge_prop_impl              false
% 15.20/2.48  --prep_def_merge_mbd                    true
% 15.20/2.48  --prep_def_merge_tr_red                 false
% 15.20/2.48  --prep_def_merge_tr_cl                  false
% 15.20/2.48  --smt_preprocessing                     true
% 15.20/2.48  --smt_ac_axioms                         fast
% 15.20/2.48  --preprocessed_out                      false
% 15.20/2.48  --preprocessed_stats                    false
% 15.20/2.48  
% 15.20/2.48  ------ Abstraction refinement Options
% 15.20/2.48  
% 15.20/2.48  --abstr_ref                             []
% 15.20/2.48  --abstr_ref_prep                        false
% 15.20/2.48  --abstr_ref_until_sat                   false
% 15.20/2.48  --abstr_ref_sig_restrict                funpre
% 15.20/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.20/2.48  --abstr_ref_under                       []
% 15.20/2.48  
% 15.20/2.48  ------ SAT Options
% 15.20/2.48  
% 15.20/2.48  --sat_mode                              false
% 15.20/2.48  --sat_fm_restart_options                ""
% 15.20/2.48  --sat_gr_def                            false
% 15.20/2.48  --sat_epr_types                         true
% 15.20/2.48  --sat_non_cyclic_types                  false
% 15.20/2.48  --sat_finite_models                     false
% 15.20/2.48  --sat_fm_lemmas                         false
% 15.20/2.48  --sat_fm_prep                           false
% 15.20/2.48  --sat_fm_uc_incr                        true
% 15.20/2.48  --sat_out_model                         small
% 15.20/2.48  --sat_out_clauses                       false
% 15.20/2.48  
% 15.20/2.48  ------ QBF Options
% 15.20/2.48  
% 15.20/2.48  --qbf_mode                              false
% 15.20/2.48  --qbf_elim_univ                         false
% 15.20/2.48  --qbf_dom_inst                          none
% 15.20/2.48  --qbf_dom_pre_inst                      false
% 15.20/2.48  --qbf_sk_in                             false
% 15.20/2.48  --qbf_pred_elim                         true
% 15.20/2.48  --qbf_split                             512
% 15.20/2.48  
% 15.20/2.48  ------ BMC1 Options
% 15.20/2.48  
% 15.20/2.48  --bmc1_incremental                      false
% 15.20/2.48  --bmc1_axioms                           reachable_all
% 15.20/2.48  --bmc1_min_bound                        0
% 15.20/2.48  --bmc1_max_bound                        -1
% 15.20/2.48  --bmc1_max_bound_default                -1
% 15.20/2.48  --bmc1_symbol_reachability              true
% 15.20/2.48  --bmc1_property_lemmas                  false
% 15.20/2.48  --bmc1_k_induction                      false
% 15.20/2.48  --bmc1_non_equiv_states                 false
% 15.20/2.48  --bmc1_deadlock                         false
% 15.20/2.48  --bmc1_ucm                              false
% 15.20/2.48  --bmc1_add_unsat_core                   none
% 15.20/2.48  --bmc1_unsat_core_children              false
% 15.20/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.20/2.48  --bmc1_out_stat                         full
% 15.20/2.48  --bmc1_ground_init                      false
% 15.20/2.48  --bmc1_pre_inst_next_state              false
% 15.20/2.48  --bmc1_pre_inst_state                   false
% 15.20/2.48  --bmc1_pre_inst_reach_state             false
% 15.20/2.48  --bmc1_out_unsat_core                   false
% 15.20/2.48  --bmc1_aig_witness_out                  false
% 15.20/2.48  --bmc1_verbose                          false
% 15.20/2.48  --bmc1_dump_clauses_tptp                false
% 15.20/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.20/2.48  --bmc1_dump_file                        -
% 15.20/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.20/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.20/2.48  --bmc1_ucm_extend_mode                  1
% 15.20/2.48  --bmc1_ucm_init_mode                    2
% 15.20/2.48  --bmc1_ucm_cone_mode                    none
% 15.20/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.20/2.48  --bmc1_ucm_relax_model                  4
% 15.20/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.20/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.20/2.48  --bmc1_ucm_layered_model                none
% 15.20/2.48  --bmc1_ucm_max_lemma_size               10
% 15.20/2.48  
% 15.20/2.48  ------ AIG Options
% 15.20/2.48  
% 15.20/2.48  --aig_mode                              false
% 15.20/2.48  
% 15.20/2.48  ------ Instantiation Options
% 15.20/2.48  
% 15.20/2.48  --instantiation_flag                    true
% 15.20/2.48  --inst_sos_flag                         true
% 15.20/2.48  --inst_sos_phase                        true
% 15.20/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.20/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.20/2.48  --inst_lit_sel_side                     none
% 15.20/2.48  --inst_solver_per_active                1400
% 15.20/2.48  --inst_solver_calls_frac                1.
% 15.20/2.48  --inst_passive_queue_type               priority_queues
% 15.20/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.20/2.48  --inst_passive_queues_freq              [25;2]
% 15.20/2.48  --inst_dismatching                      true
% 15.20/2.48  --inst_eager_unprocessed_to_passive     true
% 15.20/2.48  --inst_prop_sim_given                   true
% 15.20/2.48  --inst_prop_sim_new                     false
% 15.20/2.48  --inst_subs_new                         false
% 15.20/2.48  --inst_eq_res_simp                      false
% 15.20/2.48  --inst_subs_given                       false
% 15.20/2.48  --inst_orphan_elimination               true
% 15.20/2.48  --inst_learning_loop_flag               true
% 15.20/2.48  --inst_learning_start                   3000
% 15.20/2.48  --inst_learning_factor                  2
% 15.20/2.48  --inst_start_prop_sim_after_learn       3
% 15.20/2.48  --inst_sel_renew                        solver
% 15.20/2.48  --inst_lit_activity_flag                true
% 15.20/2.48  --inst_restr_to_given                   false
% 15.20/2.48  --inst_activity_threshold               500
% 15.20/2.48  --inst_out_proof                        true
% 15.20/2.48  
% 15.20/2.48  ------ Resolution Options
% 15.20/2.48  
% 15.20/2.48  --resolution_flag                       false
% 15.20/2.48  --res_lit_sel                           adaptive
% 15.20/2.48  --res_lit_sel_side                      none
% 15.20/2.48  --res_ordering                          kbo
% 15.20/2.48  --res_to_prop_solver                    active
% 15.20/2.48  --res_prop_simpl_new                    false
% 15.20/2.48  --res_prop_simpl_given                  true
% 15.20/2.48  --res_passive_queue_type                priority_queues
% 15.20/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.20/2.48  --res_passive_queues_freq               [15;5]
% 15.20/2.48  --res_forward_subs                      full
% 15.20/2.48  --res_backward_subs                     full
% 15.20/2.48  --res_forward_subs_resolution           true
% 15.20/2.48  --res_backward_subs_resolution          true
% 15.20/2.48  --res_orphan_elimination                true
% 15.20/2.48  --res_time_limit                        2.
% 15.20/2.48  --res_out_proof                         true
% 15.20/2.48  
% 15.20/2.48  ------ Superposition Options
% 15.20/2.48  
% 15.20/2.48  --superposition_flag                    true
% 15.20/2.48  --sup_passive_queue_type                priority_queues
% 15.20/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.20/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.20/2.48  --demod_completeness_check              fast
% 15.20/2.48  --demod_use_ground                      true
% 15.20/2.48  --sup_to_prop_solver                    passive
% 15.20/2.48  --sup_prop_simpl_new                    true
% 15.20/2.48  --sup_prop_simpl_given                  true
% 15.20/2.48  --sup_fun_splitting                     true
% 15.20/2.48  --sup_smt_interval                      50000
% 15.20/2.48  
% 15.20/2.48  ------ Superposition Simplification Setup
% 15.20/2.48  
% 15.20/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.20/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.20/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.20/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.20/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.20/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.20/2.48  --sup_immed_triv                        [TrivRules]
% 15.20/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.20/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.20/2.48  --sup_immed_bw_main                     []
% 15.20/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.20/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.20/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.20/2.48  --sup_input_bw                          []
% 15.20/2.48  
% 15.20/2.48  ------ Combination Options
% 15.20/2.48  
% 15.20/2.48  --comb_res_mult                         3
% 15.20/2.48  --comb_sup_mult                         2
% 15.20/2.48  --comb_inst_mult                        10
% 15.20/2.48  
% 15.20/2.48  ------ Debug Options
% 15.20/2.48  
% 15.20/2.48  --dbg_backtrace                         false
% 15.20/2.48  --dbg_dump_prop_clauses                 false
% 15.20/2.48  --dbg_dump_prop_clauses_file            -
% 15.20/2.48  --dbg_out_stat                          false
% 15.20/2.48  
% 15.20/2.48  
% 15.20/2.48  
% 15.20/2.48  
% 15.20/2.48  ------ Proving...
% 15.20/2.48  
% 15.20/2.48  
% 15.20/2.48  % SZS status Theorem for theBenchmark.p
% 15.20/2.48  
% 15.20/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.20/2.48  
% 15.20/2.48  fof(f10,conjecture,(
% 15.20/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))))))),
% 15.20/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.48  
% 15.20/2.48  fof(f11,negated_conjecture,(
% 15.20/2.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))))))),
% 15.20/2.48    inference(negated_conjecture,[],[f10])).
% 15.20/2.48  
% 15.20/2.48  fof(f23,plain,(
% 15.20/2.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.20/2.48    inference(ennf_transformation,[],[f11])).
% 15.20/2.48  
% 15.20/2.48  fof(f24,plain,(
% 15.20/2.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.20/2.48    inference(flattening,[],[f23])).
% 15.20/2.48  
% 15.20/2.48  fof(f27,plain,(
% 15.20/2.48    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.20/2.48    introduced(choice_axiom,[])).
% 15.20/2.48  
% 15.20/2.48  fof(f26,plain,(
% 15.20/2.48    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,sK1),k2_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.20/2.48    introduced(choice_axiom,[])).
% 15.20/2.48  
% 15.20/2.48  fof(f25,plain,(
% 15.20/2.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k2_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 15.20/2.48    introduced(choice_axiom,[])).
% 15.20/2.48  
% 15.20/2.48  fof(f28,plain,(
% 15.20/2.48    ((~r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 15.20/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 15.20/2.48  
% 15.20/2.48  fof(f41,plain,(
% 15.20/2.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.20/2.48    inference(cnf_transformation,[],[f28])).
% 15.20/2.48  
% 15.20/2.48  fof(f40,plain,(
% 15.20/2.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.20/2.48    inference(cnf_transformation,[],[f28])).
% 15.20/2.48  
% 15.20/2.48  fof(f2,axiom,(
% 15.20/2.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.20/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.48  
% 15.20/2.48  fof(f12,plain,(
% 15.20/2.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.48    inference(ennf_transformation,[],[f2])).
% 15.20/2.48  
% 15.20/2.48  fof(f30,plain,(
% 15.20/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.48    inference(cnf_transformation,[],[f12])).
% 15.20/2.48  
% 15.20/2.48  fof(f3,axiom,(
% 15.20/2.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 15.20/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.48  
% 15.20/2.48  fof(f13,plain,(
% 15.20/2.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.48    inference(ennf_transformation,[],[f3])).
% 15.20/2.48  
% 15.20/2.48  fof(f31,plain,(
% 15.20/2.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.48    inference(cnf_transformation,[],[f13])).
% 15.20/2.48  
% 15.20/2.48  fof(f7,axiom,(
% 15.20/2.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 15.20/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.48  
% 15.20/2.48  fof(f19,plain,(
% 15.20/2.48    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.48    inference(ennf_transformation,[],[f7])).
% 15.20/2.48  
% 15.20/2.48  fof(f35,plain,(
% 15.20/2.48    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.48    inference(cnf_transformation,[],[f19])).
% 15.20/2.48  
% 15.20/2.48  fof(f6,axiom,(
% 15.20/2.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 15.20/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.48  
% 15.20/2.48  fof(f18,plain,(
% 15.20/2.48    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.48    inference(ennf_transformation,[],[f6])).
% 15.20/2.48  
% 15.20/2.48  fof(f34,plain,(
% 15.20/2.48    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.48    inference(cnf_transformation,[],[f18])).
% 15.20/2.48  
% 15.20/2.48  fof(f1,axiom,(
% 15.20/2.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 15.20/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.48  
% 15.20/2.48  fof(f29,plain,(
% 15.20/2.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 15.20/2.48    inference(cnf_transformation,[],[f1])).
% 15.20/2.48  
% 15.20/2.48  fof(f8,axiom,(
% 15.20/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 15.20/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.48  
% 15.20/2.48  fof(f20,plain,(
% 15.20/2.48    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.20/2.48    inference(ennf_transformation,[],[f8])).
% 15.20/2.48  
% 15.20/2.48  fof(f36,plain,(
% 15.20/2.48    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.20/2.48    inference(cnf_transformation,[],[f20])).
% 15.20/2.48  
% 15.20/2.48  fof(f39,plain,(
% 15.20/2.48    l1_pre_topc(sK0)),
% 15.20/2.48    inference(cnf_transformation,[],[f28])).
% 15.20/2.48  
% 15.20/2.48  fof(f9,axiom,(
% 15.20/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))))))),
% 15.20/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.48  
% 15.20/2.48  fof(f21,plain,(
% 15.20/2.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.20/2.48    inference(ennf_transformation,[],[f9])).
% 15.20/2.48  
% 15.20/2.48  fof(f22,plain,(
% 15.20/2.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.20/2.48    inference(flattening,[],[f21])).
% 15.20/2.48  
% 15.20/2.48  fof(f37,plain,(
% 15.20/2.48    ( ! [X2,X0,X1] : (r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.20/2.48    inference(cnf_transformation,[],[f22])).
% 15.20/2.48  
% 15.20/2.48  fof(f38,plain,(
% 15.20/2.48    v2_pre_topc(sK0)),
% 15.20/2.48    inference(cnf_transformation,[],[f28])).
% 15.20/2.48  
% 15.20/2.48  fof(f5,axiom,(
% 15.20/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 15.20/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.48  
% 15.20/2.48  fof(f16,plain,(
% 15.20/2.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 15.20/2.48    inference(ennf_transformation,[],[f5])).
% 15.20/2.48  
% 15.20/2.48  fof(f17,plain,(
% 15.20/2.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.48    inference(flattening,[],[f16])).
% 15.20/2.48  
% 15.20/2.48  fof(f33,plain,(
% 15.20/2.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.48    inference(cnf_transformation,[],[f17])).
% 15.20/2.48  
% 15.20/2.48  fof(f4,axiom,(
% 15.20/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 15.20/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.48  
% 15.20/2.48  fof(f14,plain,(
% 15.20/2.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 15.20/2.48    inference(ennf_transformation,[],[f4])).
% 15.20/2.48  
% 15.20/2.48  fof(f15,plain,(
% 15.20/2.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.48    inference(flattening,[],[f14])).
% 15.20/2.48  
% 15.20/2.48  fof(f32,plain,(
% 15.20/2.48    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.48    inference(cnf_transformation,[],[f15])).
% 15.20/2.48  
% 15.20/2.48  fof(f42,plain,(
% 15.20/2.48    ~r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2)))),
% 15.20/2.48    inference(cnf_transformation,[],[f28])).
% 15.20/2.48  
% 15.20/2.48  cnf(c_10,negated_conjecture,
% 15.20/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.20/2.48      inference(cnf_transformation,[],[f41]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_346,negated_conjecture,
% 15.20/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_10]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_582,plain,
% 15.20/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_11,negated_conjecture,
% 15.20/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.20/2.48      inference(cnf_transformation,[],[f40]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_345,negated_conjecture,
% 15.20/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_11]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_583,plain,
% 15.20/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.48      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 15.20/2.48      inference(cnf_transformation,[],[f30]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_353,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 15.20/2.48      | k3_subset_1(X1_44,X0_44) = k4_xboole_0(X1_44,X0_44) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_1]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_575,plain,
% 15.20/2.48      ( k3_subset_1(X0_44,X1_44) = k4_xboole_0(X0_44,X1_44)
% 15.20/2.48      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_895,plain,
% 15.20/2.48      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_583,c_575]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_2,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.48      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 15.20/2.48      inference(cnf_transformation,[],[f31]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_352,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 15.20/2.48      | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_2]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_576,plain,
% 15.20/2.48      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 15.20/2.48      | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_352]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1101,plain,
% 15.20/2.48      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.20/2.48      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_895,c_576]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_16,plain,
% 15.20/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1302,plain,
% 15.20/2.48      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.20/2.48      inference(global_propositional_subsumption,
% 15.20/2.48                [status(thm)],
% 15.20/2.48                [c_1101,c_16]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_6,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.20/2.48      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 15.20/2.48      inference(cnf_transformation,[],[f35]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_348,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 15.20/2.48      | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
% 15.20/2.48      | k9_subset_1(X1_44,X0_44,k3_subset_1(X1_44,X2_44)) = k7_subset_1(X1_44,X0_44,X2_44) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_6]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_580,plain,
% 15.20/2.48      ( k9_subset_1(X0_44,X1_44,k3_subset_1(X0_44,X2_44)) = k7_subset_1(X0_44,X1_44,X2_44)
% 15.20/2.48      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top
% 15.20/2.48      | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1779,plain,
% 15.20/2.48      ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),X0_44)) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_44)
% 15.20/2.48      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_1302,c_580]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_5,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.48      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 15.20/2.48      inference(cnf_transformation,[],[f34]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_349,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 15.20/2.48      | k7_subset_1(X1_44,X0_44,X2_44) = k4_xboole_0(X0_44,X2_44) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_5]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_579,plain,
% 15.20/2.48      ( k7_subset_1(X0_44,X1_44,X2_44) = k4_xboole_0(X1_44,X2_44)
% 15.20/2.48      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1307,plain,
% 15.20/2.48      ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_44) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0_44) ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_1302,c_579]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_0,plain,
% 15.20/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.20/2.48      inference(cnf_transformation,[],[f29]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_354,plain,
% 15.20/2.48      ( k4_xboole_0(k4_xboole_0(X0_44,X1_44),X2_44) = k4_xboole_0(X0_44,k2_xboole_0(X1_44,X2_44)) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_0]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1309,plain,
% 15.20/2.48      ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0_44) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,X0_44)) ),
% 15.20/2.48      inference(demodulation,[status(thm)],[c_1307,c_354]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1780,plain,
% 15.20/2.48      ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),X0_44)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,X0_44))
% 15.20/2.48      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(light_normalisation,[status(thm)],[c_1779,c_1309]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_39860,plain,
% 15.20/2.48      ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_582,c_1780]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_894,plain,
% 15.20/2.48      ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_582,c_575]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_39905,plain,
% 15.20/2.48      ( k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
% 15.20/2.48      inference(light_normalisation,[status(thm)],[c_39860,c_894]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_7,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.20/2.48      | ~ l1_pre_topc(X1)
% 15.20/2.48      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 15.20/2.48      inference(cnf_transformation,[],[f36]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_12,negated_conjecture,
% 15.20/2.48      ( l1_pre_topc(sK0) ),
% 15.20/2.48      inference(cnf_transformation,[],[f39]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_206,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.20/2.48      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
% 15.20/2.48      | sK0 != X1 ),
% 15.20/2.48      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_207,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.48      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0) ),
% 15.20/2.48      inference(unflattening,[status(thm)],[c_206]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_343,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.48      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0_44)) = k2_tops_1(sK0,X0_44) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_207]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_585,plain,
% 15.20/2.48      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0_44)) = k2_tops_1(sK0,X0_44)
% 15.20/2.48      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_699,plain,
% 15.20/2.48      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k2_tops_1(sK0,sK2) ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_582,c_585]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_700,plain,
% 15.20/2.48      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_583,c_585]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_8,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
% 15.20/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.20/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 15.20/2.48      | ~ v2_pre_topc(X0)
% 15.20/2.48      | ~ l1_pre_topc(X0) ),
% 15.20/2.48      inference(cnf_transformation,[],[f37]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_13,negated_conjecture,
% 15.20/2.48      ( v2_pre_topc(sK0) ),
% 15.20/2.48      inference(cnf_transformation,[],[f38]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_181,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
% 15.20/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 15.20/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 15.20/2.48      | ~ l1_pre_topc(X0)
% 15.20/2.48      | sK0 != X0 ),
% 15.20/2.48      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_182,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,X1)))
% 15.20/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.48      | ~ l1_pre_topc(sK0) ),
% 15.20/2.48      inference(unflattening,[status(thm)],[c_181]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_186,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.48      | r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,X1))) ),
% 15.20/2.48      inference(global_propositional_subsumption,
% 15.20/2.48                [status(thm)],
% 15.20/2.48                [c_182,c_12]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_187,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,X1)))
% 15.20/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.20/2.48      inference(renaming,[status(thm)],[c_186]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_344,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0_44,X1_44)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_44),k2_tops_1(sK0,X1_44)))
% 15.20/2.48      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.48      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_187]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_584,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0_44,X1_44)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0_44),k2_tops_1(sK0,X1_44))) = iProver_top
% 15.20/2.48      | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.20/2.48      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_830,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0_44)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,X0_44))) = iProver_top
% 15.20/2.48      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.20/2.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_700,c_584]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_848,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top
% 15.20/2.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.20/2.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_699,c_830]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1027,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_44),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.20/2.48      inference(instantiation,[status(thm)],[c_352]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1028,plain,
% 15.20/2.48      ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.20/2.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_44),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_1027]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1030,plain,
% 15.20/2.48      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.20/2.48      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(instantiation,[status(thm)],[c_1028]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_6376,plain,
% 15.20/2.48      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.20/2.48      | r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top ),
% 15.20/2.48      inference(global_propositional_subsumption,
% 15.20/2.48                [status(thm)],
% 15.20/2.48                [c_848,c_16,c_1030]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_6377,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top
% 15.20/2.48      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(renaming,[status(thm)],[c_6376]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_6380,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top
% 15.20/2.48      | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(light_normalisation,[status(thm)],[c_6377,c_894,c_895]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_17,plain,
% 15.20/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1042,plain,
% 15.20/2.48      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.20/2.48      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_894,c_576]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_6382,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top ),
% 15.20/2.48      inference(global_propositional_subsumption,
% 15.20/2.48                [status(thm)],
% 15.20/2.48                [c_6380,c_17,c_1042]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_41309,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top ),
% 15.20/2.48      inference(demodulation,[status(thm)],[c_39905,c_6382]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_4,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.20/2.48      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 15.20/2.48      inference(cnf_transformation,[],[f33]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_350,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 15.20/2.48      | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
% 15.20/2.48      | k4_subset_1(X1_44,X0_44,X2_44) = k2_xboole_0(X0_44,X2_44) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_4]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_578,plain,
% 15.20/2.48      ( k4_subset_1(X0_44,X1_44,X2_44) = k2_xboole_0(X1_44,X2_44)
% 15.20/2.48      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top
% 15.20/2.48      | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1419,plain,
% 15.20/2.48      ( k4_subset_1(u1_struct_0(sK0),sK1,X0_44) = k2_xboole_0(sK1,X0_44)
% 15.20/2.48      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_583,c_578]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1558,plain,
% 15.20/2.48      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_582,c_1419]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_3,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.20/2.48      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 15.20/2.48      inference(cnf_transformation,[],[f32]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_351,plain,
% 15.20/2.48      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 15.20/2.48      | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
% 15.20/2.48      | m1_subset_1(k4_subset_1(X1_44,X0_44,X2_44),k1_zfmisc_1(X1_44)) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_3]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_577,plain,
% 15.20/2.48      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 15.20/2.48      | m1_subset_1(X2_44,k1_zfmisc_1(X1_44)) != iProver_top
% 15.20/2.48      | m1_subset_1(k4_subset_1(X1_44,X0_44,X2_44),k1_zfmisc_1(X1_44)) = iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1622,plain,
% 15.20/2.48      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.20/2.48      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.20/2.48      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_1558,c_577]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_4212,plain,
% 15.20/2.48      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.20/2.48      inference(global_propositional_subsumption,
% 15.20/2.48                [status(thm)],
% 15.20/2.48                [c_1622,c_16,c_17]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_4223,plain,
% 15.20/2.48      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_4212,c_585]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_4229,plain,
% 15.20/2.48      ( k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
% 15.20/2.48      inference(superposition,[status(thm)],[c_4212,c_575]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_4234,plain,
% 15.20/2.48      ( k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.20/2.48      inference(demodulation,[status(thm)],[c_4223,c_4229]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_41310,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) = iProver_top ),
% 15.20/2.48      inference(light_normalisation,[status(thm)],[c_41309,c_4234]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_9,negated_conjecture,
% 15.20/2.48      ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) ),
% 15.20/2.48      inference(cnf_transformation,[],[f42]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_347,negated_conjecture,
% 15.20/2.48      ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) ),
% 15.20/2.48      inference(subtyping,[status(esa)],[c_9]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_581,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) != iProver_top ),
% 15.20/2.48      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(c_1620,plain,
% 15.20/2.48      ( r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) != iProver_top ),
% 15.20/2.48      inference(demodulation,[status(thm)],[c_1558,c_581]) ).
% 15.20/2.48  
% 15.20/2.48  cnf(contradiction,plain,
% 15.20/2.48      ( $false ),
% 15.20/2.48      inference(minisat,[status(thm)],[c_41310,c_1620]) ).
% 15.20/2.48  
% 15.20/2.48  
% 15.20/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.20/2.48  
% 15.20/2.48  ------                               Statistics
% 15.20/2.48  
% 15.20/2.48  ------ General
% 15.20/2.48  
% 15.20/2.48  abstr_ref_over_cycles:                  0
% 15.20/2.48  abstr_ref_under_cycles:                 0
% 15.20/2.48  gc_basic_clause_elim:                   0
% 15.20/2.48  forced_gc_time:                         0
% 15.20/2.48  parsing_time:                           0.009
% 15.20/2.48  unif_index_cands_time:                  0.
% 15.20/2.48  unif_index_add_time:                    0.
% 15.20/2.48  orderings_time:                         0.
% 15.20/2.48  out_proof_time:                         0.01
% 15.20/2.48  total_time:                             1.556
% 15.20/2.48  num_of_symbols:                         50
% 15.20/2.48  num_of_terms:                           32729
% 15.20/2.48  
% 15.20/2.48  ------ Preprocessing
% 15.20/2.48  
% 15.20/2.48  num_of_splits:                          0
% 15.20/2.48  num_of_split_atoms:                     0
% 15.20/2.48  num_of_reused_defs:                     0
% 15.20/2.48  num_eq_ax_congr_red:                    23
% 15.20/2.48  num_of_sem_filtered_clauses:            1
% 15.20/2.48  num_of_subtypes:                        3
% 15.20/2.48  monotx_restored_types:                  0
% 15.20/2.48  sat_num_of_epr_types:                   0
% 15.20/2.48  sat_num_of_non_cyclic_types:            0
% 15.20/2.48  sat_guarded_non_collapsed_types:        0
% 15.20/2.48  num_pure_diseq_elim:                    0
% 15.20/2.48  simp_replaced_by:                       0
% 15.20/2.48  res_preprocessed:                       73
% 15.20/2.48  prep_upred:                             0
% 15.20/2.48  prep_unflattend:                        2
% 15.20/2.48  smt_new_axioms:                         0
% 15.20/2.48  pred_elim_cands:                        2
% 15.20/2.48  pred_elim:                              2
% 15.20/2.48  pred_elim_cl:                           2
% 15.20/2.48  pred_elim_cycles:                       5
% 15.20/2.48  merged_defs:                            0
% 15.20/2.48  merged_defs_ncl:                        0
% 15.20/2.48  bin_hyper_res:                          0
% 15.20/2.48  prep_cycles:                            4
% 15.20/2.48  pred_elim_time:                         0.002
% 15.20/2.48  splitting_time:                         0.
% 15.20/2.48  sem_filter_time:                        0.
% 15.20/2.48  monotx_time:                            0.
% 15.20/2.48  subtype_inf_time:                       0.
% 15.20/2.48  
% 15.20/2.48  ------ Problem properties
% 15.20/2.48  
% 15.20/2.48  clauses:                                12
% 15.20/2.48  conjectures:                            3
% 15.20/2.48  epr:                                    0
% 15.20/2.48  horn:                                   12
% 15.20/2.48  ground:                                 3
% 15.20/2.48  unary:                                  4
% 15.20/2.48  binary:                                 4
% 15.20/2.48  lits:                                   24
% 15.20/2.48  lits_eq:                                6
% 15.20/2.48  fd_pure:                                0
% 15.20/2.48  fd_pseudo:                              0
% 15.20/2.48  fd_cond:                                0
% 15.20/2.48  fd_pseudo_cond:                         0
% 15.20/2.48  ac_symbols:                             0
% 15.20/2.48  
% 15.20/2.48  ------ Propositional Solver
% 15.20/2.48  
% 15.20/2.48  prop_solver_calls:                      37
% 15.20/2.48  prop_fast_solver_calls:                 828
% 15.20/2.48  smt_solver_calls:                       0
% 15.20/2.48  smt_fast_solver_calls:                  0
% 15.20/2.48  prop_num_of_clauses:                    8290
% 15.20/2.48  prop_preprocess_simplified:             10521
% 15.20/2.48  prop_fo_subsumed:                       34
% 15.20/2.48  prop_solver_time:                       0.
% 15.20/2.48  smt_solver_time:                        0.
% 15.20/2.48  smt_fast_solver_time:                   0.
% 15.20/2.48  prop_fast_solver_time:                  0.
% 15.20/2.48  prop_unsat_core_time:                   0.001
% 15.20/2.48  
% 15.20/2.48  ------ QBF
% 15.20/2.48  
% 15.20/2.48  qbf_q_res:                              0
% 15.20/2.48  qbf_num_tautologies:                    0
% 15.20/2.48  qbf_prep_cycles:                        0
% 15.20/2.48  
% 15.20/2.48  ------ BMC1
% 15.20/2.48  
% 15.20/2.48  bmc1_current_bound:                     -1
% 15.20/2.48  bmc1_last_solved_bound:                 -1
% 15.20/2.48  bmc1_unsat_core_size:                   -1
% 15.20/2.48  bmc1_unsat_core_parents_size:           -1
% 15.20/2.48  bmc1_merge_next_fun:                    0
% 15.20/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.20/2.48  
% 15.20/2.48  ------ Instantiation
% 15.20/2.48  
% 15.20/2.48  inst_num_of_clauses:                    2904
% 15.20/2.48  inst_num_in_passive:                    868
% 15.20/2.48  inst_num_in_active:                     1501
% 15.20/2.48  inst_num_in_unprocessed:                535
% 15.20/2.48  inst_num_of_loops:                      1620
% 15.20/2.48  inst_num_of_learning_restarts:          0
% 15.20/2.48  inst_num_moves_active_passive:          106
% 15.20/2.48  inst_lit_activity:                      0
% 15.20/2.48  inst_lit_activity_moves:                0
% 15.20/2.48  inst_num_tautologies:                   0
% 15.20/2.48  inst_num_prop_implied:                  0
% 15.20/2.48  inst_num_existing_simplified:           0
% 15.20/2.48  inst_num_eq_res_simplified:             0
% 15.20/2.48  inst_num_child_elim:                    0
% 15.20/2.48  inst_num_of_dismatching_blockings:      14623
% 15.20/2.48  inst_num_of_non_proper_insts:           12515
% 15.20/2.48  inst_num_of_duplicates:                 0
% 15.20/2.48  inst_inst_num_from_inst_to_res:         0
% 15.20/2.48  inst_dismatching_checking_time:         0.
% 15.20/2.48  
% 15.20/2.48  ------ Resolution
% 15.20/2.48  
% 15.20/2.48  res_num_of_clauses:                     0
% 15.20/2.48  res_num_in_passive:                     0
% 15.20/2.48  res_num_in_active:                      0
% 15.20/2.48  res_num_of_loops:                       77
% 15.20/2.48  res_forward_subset_subsumed:            589
% 15.20/2.48  res_backward_subset_subsumed:           8
% 15.20/2.48  res_forward_subsumed:                   0
% 15.20/2.48  res_backward_subsumed:                  0
% 15.20/2.48  res_forward_subsumption_resolution:     0
% 15.20/2.48  res_backward_subsumption_resolution:    0
% 15.20/2.48  res_clause_to_clause_subsumption:       3669
% 15.20/2.48  res_orphan_elimination:                 0
% 15.20/2.48  res_tautology_del:                      1325
% 15.20/2.48  res_num_eq_res_simplified:              0
% 15.20/2.48  res_num_sel_changes:                    0
% 15.20/2.48  res_moves_from_active_to_pass:          0
% 15.20/2.48  
% 15.20/2.48  ------ Superposition
% 15.20/2.48  
% 15.20/2.48  sup_time_total:                         0.
% 15.20/2.48  sup_time_generating:                    0.
% 15.20/2.48  sup_time_sim_full:                      0.
% 15.20/2.48  sup_time_sim_immed:                     0.
% 15.20/2.48  
% 15.20/2.48  sup_num_of_clauses:                     1554
% 15.20/2.48  sup_num_in_active:                      289
% 15.20/2.48  sup_num_in_passive:                     1265
% 15.20/2.48  sup_num_of_loops:                       323
% 15.20/2.48  sup_fw_superposition:                   936
% 15.20/2.48  sup_bw_superposition:                   866
% 15.20/2.48  sup_immediate_simplified:               850
% 15.20/2.48  sup_given_eliminated:                   0
% 15.20/2.48  comparisons_done:                       0
% 15.20/2.48  comparisons_avoided:                    0
% 15.20/2.48  
% 15.20/2.48  ------ Simplifications
% 15.20/2.48  
% 15.20/2.48  
% 15.20/2.48  sim_fw_subset_subsumed:                 3
% 15.20/2.48  sim_bw_subset_subsumed:                 2
% 15.20/2.48  sim_fw_subsumed:                        23
% 15.20/2.48  sim_bw_subsumed:                        0
% 15.20/2.48  sim_fw_subsumption_res:                 0
% 15.20/2.48  sim_bw_subsumption_res:                 0
% 15.20/2.48  sim_tautology_del:                      0
% 15.20/2.48  sim_eq_tautology_del:                   97
% 15.20/2.48  sim_eq_res_simp:                        0
% 15.20/2.48  sim_fw_demodulated:                     266
% 15.20/2.48  sim_bw_demodulated:                     34
% 15.20/2.48  sim_light_normalised:                   610
% 15.20/2.48  sim_joinable_taut:                      0
% 15.20/2.48  sim_joinable_simp:                      0
% 15.20/2.48  sim_ac_normalised:                      0
% 15.20/2.48  sim_smt_subsumption:                    0
% 15.20/2.48  
%------------------------------------------------------------------------------
