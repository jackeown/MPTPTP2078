%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:56 EST 2020

% Result     : Theorem 15.67s
% Output     : CNFRefutation 15.67s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 273 expanded)
%              Number of clauses        :   70 ( 108 expanded)
%              Number of leaves         :   14 (  67 expanded)
%              Depth                    :   20
%              Number of atoms          :  271 ( 851 expanded)
%              Number of equality atoms :   55 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_316,plain,
    ( ~ r1_xboole_0(X0_40,X1_40)
    | r1_xboole_0(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_857,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,X0_40),k4_xboole_0(X1_40,X0_40))
    | r1_xboole_0(k4_xboole_0(X1_40,X0_40),k1_tops_1(sK0,X0_40)) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_54575,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(X0_40,sK2))
    | r1_xboole_0(k4_xboole_0(X0_40,sK2),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_54579,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))
    | r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_54575])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_313,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_xboole_0(X0_40,k4_xboole_0(X2_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_685,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0_40),X0_40)
    | r1_xboole_0(k1_tops_1(sK0,X0_40),k4_xboole_0(X1_40,X0_40)) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_33141,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_307,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_590,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
    | k7_subset_1(X0_42,X0_40,X1_40) = k4_xboole_0(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_587,plain,
    ( k7_subset_1(X0_42,X0_40,X1_40) = k4_xboole_0(X0_40,X1_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_1095,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0_40) = k4_xboole_0(sK1,X0_40) ),
    inference(superposition,[status(thm)],[c_590,c_587])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
    | m1_subset_1(k7_subset_1(X0_42,X0_40,X1_40),k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_586,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top
    | m1_subset_1(k7_subset_1(X0_42,X0_40,X1_40),k1_zfmisc_1(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_1348,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1095,c_586])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1669,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_15])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_175,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0_40),X0_40) ),
    inference(subtyping,[status(esa)],[c_176])).

cnf(c_592,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_40),X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_1676,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0_40)),k4_xboole_0(sK1,X0_40)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1669,c_592])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_314,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ r1_xboole_0(X1_40,X2_40)
    | r1_xboole_0(X0_40,X2_40) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_583,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_xboole_0(X1_40,X2_40) != iProver_top
    | r1_xboole_0(X0_40,X2_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_1853,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0_40)),X1_40) = iProver_top
    | r1_xboole_0(k4_xboole_0(sK1,X0_40),X1_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_583])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_157,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_158,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_157])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_40,X0_40)
    | r1_tarski(k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)) ),
    inference(subtyping,[status(esa)],[c_158])).

cnf(c_591,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_40,X0_40) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_312,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(X0_40,k4_xboole_0(X1_40,X2_40))
    | ~ r1_xboole_0(X0_40,X2_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_585,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(X0_40,k4_xboole_0(X1_40,X2_40)) = iProver_top
    | r1_xboole_0(X0_40,X2_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_187,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_188,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_187])).

cnf(c_304,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_188])).

cnf(c_593,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_1096,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_40),X1_40) = k4_xboole_0(k1_tops_1(sK0,X0_40),X1_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_587])).

cnf(c_2748,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0_40) = k4_xboole_0(k1_tops_1(sK0,sK1),X0_40) ),
    inference(superposition,[status(thm)],[c_590,c_1096])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_309,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_588,plain,
    ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_1346,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1095,c_588])).

cnf(c_2868,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2748,c_1346])).

cnf(c_2876,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_585,c_2868])).

cnf(c_12880,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_2876])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_315,plain,
    ( r1_tarski(k4_xboole_0(X0_40,X1_40),X0_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_14222,plain,
    ( r1_tarski(k4_xboole_0(X0_40,sK2),X0_40) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_14223,plain,
    ( r1_tarski(k4_xboole_0(X0_40,sK2),X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14222])).

cnf(c_14225,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_14223])).

cnf(c_24930,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12880,c_15,c_14225])).

cnf(c_24936,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24930,c_1669])).

cnf(c_24940,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1853,c_24936])).

cnf(c_24969,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_24940])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_308,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_589,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_773,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_589,c_592])).

cnf(c_779,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_773])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54579,c_33141,c_24969,c_779])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:16:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.67/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.67/2.48  
% 15.67/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.67/2.48  
% 15.67/2.48  ------  iProver source info
% 15.67/2.48  
% 15.67/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.67/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.67/2.48  git: non_committed_changes: false
% 15.67/2.48  git: last_make_outside_of_git: false
% 15.67/2.48  
% 15.67/2.48  ------ 
% 15.67/2.48  
% 15.67/2.48  ------ Input Options
% 15.67/2.48  
% 15.67/2.48  --out_options                           all
% 15.67/2.48  --tptp_safe_out                         true
% 15.67/2.48  --problem_path                          ""
% 15.67/2.48  --include_path                          ""
% 15.67/2.48  --clausifier                            res/vclausify_rel
% 15.67/2.48  --clausifier_options                    --mode clausify
% 15.67/2.48  --stdin                                 false
% 15.67/2.48  --stats_out                             all
% 15.67/2.48  
% 15.67/2.48  ------ General Options
% 15.67/2.48  
% 15.67/2.48  --fof                                   false
% 15.67/2.48  --time_out_real                         305.
% 15.67/2.48  --time_out_virtual                      -1.
% 15.67/2.48  --symbol_type_check                     false
% 15.67/2.48  --clausify_out                          false
% 15.67/2.48  --sig_cnt_out                           false
% 15.67/2.48  --trig_cnt_out                          false
% 15.67/2.48  --trig_cnt_out_tolerance                1.
% 15.67/2.48  --trig_cnt_out_sk_spl                   false
% 15.67/2.48  --abstr_cl_out                          false
% 15.67/2.48  
% 15.67/2.48  ------ Global Options
% 15.67/2.48  
% 15.67/2.48  --schedule                              default
% 15.67/2.48  --add_important_lit                     false
% 15.67/2.48  --prop_solver_per_cl                    1000
% 15.67/2.48  --min_unsat_core                        false
% 15.67/2.48  --soft_assumptions                      false
% 15.67/2.48  --soft_lemma_size                       3
% 15.67/2.48  --prop_impl_unit_size                   0
% 15.67/2.48  --prop_impl_unit                        []
% 15.67/2.48  --share_sel_clauses                     true
% 15.67/2.48  --reset_solvers                         false
% 15.67/2.48  --bc_imp_inh                            [conj_cone]
% 15.67/2.48  --conj_cone_tolerance                   3.
% 15.67/2.48  --extra_neg_conj                        none
% 15.67/2.48  --large_theory_mode                     true
% 15.67/2.48  --prolific_symb_bound                   200
% 15.67/2.48  --lt_threshold                          2000
% 15.67/2.48  --clause_weak_htbl                      true
% 15.67/2.48  --gc_record_bc_elim                     false
% 15.67/2.48  
% 15.67/2.48  ------ Preprocessing Options
% 15.67/2.48  
% 15.67/2.48  --preprocessing_flag                    true
% 15.67/2.48  --time_out_prep_mult                    0.1
% 15.67/2.48  --splitting_mode                        input
% 15.67/2.48  --splitting_grd                         true
% 15.67/2.48  --splitting_cvd                         false
% 15.67/2.48  --splitting_cvd_svl                     false
% 15.67/2.48  --splitting_nvd                         32
% 15.67/2.48  --sub_typing                            true
% 15.67/2.48  --prep_gs_sim                           true
% 15.67/2.48  --prep_unflatten                        true
% 15.67/2.48  --prep_res_sim                          true
% 15.67/2.48  --prep_upred                            true
% 15.67/2.48  --prep_sem_filter                       exhaustive
% 15.67/2.48  --prep_sem_filter_out                   false
% 15.67/2.48  --pred_elim                             true
% 15.67/2.48  --res_sim_input                         true
% 15.67/2.48  --eq_ax_congr_red                       true
% 15.67/2.48  --pure_diseq_elim                       true
% 15.67/2.48  --brand_transform                       false
% 15.67/2.48  --non_eq_to_eq                          false
% 15.67/2.48  --prep_def_merge                        true
% 15.67/2.48  --prep_def_merge_prop_impl              false
% 15.67/2.48  --prep_def_merge_mbd                    true
% 15.67/2.48  --prep_def_merge_tr_red                 false
% 15.67/2.48  --prep_def_merge_tr_cl                  false
% 15.67/2.48  --smt_preprocessing                     true
% 15.67/2.48  --smt_ac_axioms                         fast
% 15.67/2.48  --preprocessed_out                      false
% 15.67/2.48  --preprocessed_stats                    false
% 15.67/2.48  
% 15.67/2.48  ------ Abstraction refinement Options
% 15.67/2.48  
% 15.67/2.48  --abstr_ref                             []
% 15.67/2.48  --abstr_ref_prep                        false
% 15.67/2.48  --abstr_ref_until_sat                   false
% 15.67/2.48  --abstr_ref_sig_restrict                funpre
% 15.67/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.67/2.48  --abstr_ref_under                       []
% 15.67/2.48  
% 15.67/2.48  ------ SAT Options
% 15.67/2.48  
% 15.67/2.48  --sat_mode                              false
% 15.67/2.48  --sat_fm_restart_options                ""
% 15.67/2.48  --sat_gr_def                            false
% 15.67/2.48  --sat_epr_types                         true
% 15.67/2.48  --sat_non_cyclic_types                  false
% 15.67/2.48  --sat_finite_models                     false
% 15.67/2.48  --sat_fm_lemmas                         false
% 15.67/2.48  --sat_fm_prep                           false
% 15.67/2.48  --sat_fm_uc_incr                        true
% 15.67/2.48  --sat_out_model                         small
% 15.67/2.48  --sat_out_clauses                       false
% 15.67/2.48  
% 15.67/2.48  ------ QBF Options
% 15.67/2.48  
% 15.67/2.48  --qbf_mode                              false
% 15.67/2.48  --qbf_elim_univ                         false
% 15.67/2.48  --qbf_dom_inst                          none
% 15.67/2.48  --qbf_dom_pre_inst                      false
% 15.67/2.48  --qbf_sk_in                             false
% 15.67/2.48  --qbf_pred_elim                         true
% 15.67/2.48  --qbf_split                             512
% 15.67/2.48  
% 15.67/2.48  ------ BMC1 Options
% 15.67/2.48  
% 15.67/2.48  --bmc1_incremental                      false
% 15.67/2.48  --bmc1_axioms                           reachable_all
% 15.67/2.48  --bmc1_min_bound                        0
% 15.67/2.48  --bmc1_max_bound                        -1
% 15.67/2.48  --bmc1_max_bound_default                -1
% 15.67/2.48  --bmc1_symbol_reachability              true
% 15.67/2.48  --bmc1_property_lemmas                  false
% 15.67/2.48  --bmc1_k_induction                      false
% 15.67/2.48  --bmc1_non_equiv_states                 false
% 15.67/2.48  --bmc1_deadlock                         false
% 15.67/2.48  --bmc1_ucm                              false
% 15.67/2.48  --bmc1_add_unsat_core                   none
% 15.67/2.48  --bmc1_unsat_core_children              false
% 15.67/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.67/2.48  --bmc1_out_stat                         full
% 15.67/2.48  --bmc1_ground_init                      false
% 15.67/2.48  --bmc1_pre_inst_next_state              false
% 15.67/2.48  --bmc1_pre_inst_state                   false
% 15.67/2.48  --bmc1_pre_inst_reach_state             false
% 15.67/2.48  --bmc1_out_unsat_core                   false
% 15.67/2.48  --bmc1_aig_witness_out                  false
% 15.67/2.48  --bmc1_verbose                          false
% 15.67/2.48  --bmc1_dump_clauses_tptp                false
% 15.67/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.67/2.48  --bmc1_dump_file                        -
% 15.67/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.67/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.67/2.48  --bmc1_ucm_extend_mode                  1
% 15.67/2.48  --bmc1_ucm_init_mode                    2
% 15.67/2.48  --bmc1_ucm_cone_mode                    none
% 15.67/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.67/2.48  --bmc1_ucm_relax_model                  4
% 15.67/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.67/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.67/2.48  --bmc1_ucm_layered_model                none
% 15.67/2.48  --bmc1_ucm_max_lemma_size               10
% 15.67/2.48  
% 15.67/2.48  ------ AIG Options
% 15.67/2.48  
% 15.67/2.48  --aig_mode                              false
% 15.67/2.48  
% 15.67/2.48  ------ Instantiation Options
% 15.67/2.48  
% 15.67/2.48  --instantiation_flag                    true
% 15.67/2.48  --inst_sos_flag                         false
% 15.67/2.48  --inst_sos_phase                        true
% 15.67/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.67/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.67/2.48  --inst_lit_sel_side                     num_symb
% 15.67/2.48  --inst_solver_per_active                1400
% 15.67/2.48  --inst_solver_calls_frac                1.
% 15.67/2.48  --inst_passive_queue_type               priority_queues
% 15.67/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.67/2.48  --inst_passive_queues_freq              [25;2]
% 15.67/2.48  --inst_dismatching                      true
% 15.67/2.48  --inst_eager_unprocessed_to_passive     true
% 15.67/2.48  --inst_prop_sim_given                   true
% 15.67/2.48  --inst_prop_sim_new                     false
% 15.67/2.48  --inst_subs_new                         false
% 15.67/2.48  --inst_eq_res_simp                      false
% 15.67/2.48  --inst_subs_given                       false
% 15.67/2.48  --inst_orphan_elimination               true
% 15.67/2.48  --inst_learning_loop_flag               true
% 15.67/2.48  --inst_learning_start                   3000
% 15.67/2.48  --inst_learning_factor                  2
% 15.67/2.48  --inst_start_prop_sim_after_learn       3
% 15.67/2.48  --inst_sel_renew                        solver
% 15.67/2.48  --inst_lit_activity_flag                true
% 15.67/2.48  --inst_restr_to_given                   false
% 15.67/2.48  --inst_activity_threshold               500
% 15.67/2.48  --inst_out_proof                        true
% 15.67/2.48  
% 15.67/2.48  ------ Resolution Options
% 15.67/2.48  
% 15.67/2.48  --resolution_flag                       true
% 15.67/2.48  --res_lit_sel                           adaptive
% 15.67/2.48  --res_lit_sel_side                      none
% 15.67/2.48  --res_ordering                          kbo
% 15.67/2.48  --res_to_prop_solver                    active
% 15.67/2.48  --res_prop_simpl_new                    false
% 15.67/2.48  --res_prop_simpl_given                  true
% 15.67/2.48  --res_passive_queue_type                priority_queues
% 15.67/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.67/2.48  --res_passive_queues_freq               [15;5]
% 15.67/2.48  --res_forward_subs                      full
% 15.67/2.48  --res_backward_subs                     full
% 15.67/2.48  --res_forward_subs_resolution           true
% 15.67/2.48  --res_backward_subs_resolution          true
% 15.67/2.48  --res_orphan_elimination                true
% 15.67/2.48  --res_time_limit                        2.
% 15.67/2.48  --res_out_proof                         true
% 15.67/2.48  
% 15.67/2.48  ------ Superposition Options
% 15.67/2.48  
% 15.67/2.48  --superposition_flag                    true
% 15.67/2.48  --sup_passive_queue_type                priority_queues
% 15.67/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.67/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.67/2.48  --demod_completeness_check              fast
% 15.67/2.48  --demod_use_ground                      true
% 15.67/2.48  --sup_to_prop_solver                    passive
% 15.67/2.48  --sup_prop_simpl_new                    true
% 15.67/2.48  --sup_prop_simpl_given                  true
% 15.67/2.48  --sup_fun_splitting                     false
% 15.67/2.48  --sup_smt_interval                      50000
% 15.67/2.48  
% 15.67/2.48  ------ Superposition Simplification Setup
% 15.67/2.48  
% 15.67/2.48  --sup_indices_passive                   []
% 15.67/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.67/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.48  --sup_full_bw                           [BwDemod]
% 15.67/2.48  --sup_immed_triv                        [TrivRules]
% 15.67/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.67/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.48  --sup_immed_bw_main                     []
% 15.67/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.67/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.67/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.67/2.48  
% 15.67/2.48  ------ Combination Options
% 15.67/2.48  
% 15.67/2.48  --comb_res_mult                         3
% 15.67/2.48  --comb_sup_mult                         2
% 15.67/2.48  --comb_inst_mult                        10
% 15.67/2.48  
% 15.67/2.48  ------ Debug Options
% 15.67/2.48  
% 15.67/2.48  --dbg_backtrace                         false
% 15.67/2.48  --dbg_dump_prop_clauses                 false
% 15.67/2.48  --dbg_dump_prop_clauses_file            -
% 15.67/2.48  --dbg_out_stat                          false
% 15.67/2.48  ------ Parsing...
% 15.67/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.67/2.48  
% 15.67/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.67/2.48  
% 15.67/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.67/2.48  
% 15.67/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.67/2.48  ------ Proving...
% 15.67/2.48  ------ Problem Properties 
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  clauses                                 13
% 15.67/2.48  conjectures                             3
% 15.67/2.48  EPR                                     2
% 15.67/2.48  Horn                                    13
% 15.67/2.48  unary                                   4
% 15.67/2.48  binary                                  6
% 15.67/2.48  lits                                    26
% 15.67/2.48  lits eq                                 1
% 15.67/2.48  fd_pure                                 0
% 15.67/2.48  fd_pseudo                               0
% 15.67/2.48  fd_cond                                 0
% 15.67/2.48  fd_pseudo_cond                          0
% 15.67/2.48  AC symbols                              0
% 15.67/2.48  
% 15.67/2.48  ------ Schedule dynamic 5 is on 
% 15.67/2.48  
% 15.67/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  ------ 
% 15.67/2.48  Current options:
% 15.67/2.48  ------ 
% 15.67/2.48  
% 15.67/2.48  ------ Input Options
% 15.67/2.48  
% 15.67/2.48  --out_options                           all
% 15.67/2.48  --tptp_safe_out                         true
% 15.67/2.48  --problem_path                          ""
% 15.67/2.48  --include_path                          ""
% 15.67/2.48  --clausifier                            res/vclausify_rel
% 15.67/2.48  --clausifier_options                    --mode clausify
% 15.67/2.48  --stdin                                 false
% 15.67/2.48  --stats_out                             all
% 15.67/2.48  
% 15.67/2.48  ------ General Options
% 15.67/2.48  
% 15.67/2.48  --fof                                   false
% 15.67/2.48  --time_out_real                         305.
% 15.67/2.48  --time_out_virtual                      -1.
% 15.67/2.48  --symbol_type_check                     false
% 15.67/2.48  --clausify_out                          false
% 15.67/2.48  --sig_cnt_out                           false
% 15.67/2.48  --trig_cnt_out                          false
% 15.67/2.48  --trig_cnt_out_tolerance                1.
% 15.67/2.48  --trig_cnt_out_sk_spl                   false
% 15.67/2.48  --abstr_cl_out                          false
% 15.67/2.48  
% 15.67/2.48  ------ Global Options
% 15.67/2.48  
% 15.67/2.48  --schedule                              default
% 15.67/2.48  --add_important_lit                     false
% 15.67/2.48  --prop_solver_per_cl                    1000
% 15.67/2.48  --min_unsat_core                        false
% 15.67/2.48  --soft_assumptions                      false
% 15.67/2.48  --soft_lemma_size                       3
% 15.67/2.48  --prop_impl_unit_size                   0
% 15.67/2.48  --prop_impl_unit                        []
% 15.67/2.48  --share_sel_clauses                     true
% 15.67/2.48  --reset_solvers                         false
% 15.67/2.48  --bc_imp_inh                            [conj_cone]
% 15.67/2.48  --conj_cone_tolerance                   3.
% 15.67/2.48  --extra_neg_conj                        none
% 15.67/2.48  --large_theory_mode                     true
% 15.67/2.48  --prolific_symb_bound                   200
% 15.67/2.48  --lt_threshold                          2000
% 15.67/2.48  --clause_weak_htbl                      true
% 15.67/2.48  --gc_record_bc_elim                     false
% 15.67/2.48  
% 15.67/2.48  ------ Preprocessing Options
% 15.67/2.48  
% 15.67/2.48  --preprocessing_flag                    true
% 15.67/2.48  --time_out_prep_mult                    0.1
% 15.67/2.48  --splitting_mode                        input
% 15.67/2.48  --splitting_grd                         true
% 15.67/2.48  --splitting_cvd                         false
% 15.67/2.48  --splitting_cvd_svl                     false
% 15.67/2.48  --splitting_nvd                         32
% 15.67/2.48  --sub_typing                            true
% 15.67/2.48  --prep_gs_sim                           true
% 15.67/2.48  --prep_unflatten                        true
% 15.67/2.48  --prep_res_sim                          true
% 15.67/2.48  --prep_upred                            true
% 15.67/2.48  --prep_sem_filter                       exhaustive
% 15.67/2.48  --prep_sem_filter_out                   false
% 15.67/2.48  --pred_elim                             true
% 15.67/2.48  --res_sim_input                         true
% 15.67/2.48  --eq_ax_congr_red                       true
% 15.67/2.48  --pure_diseq_elim                       true
% 15.67/2.48  --brand_transform                       false
% 15.67/2.48  --non_eq_to_eq                          false
% 15.67/2.48  --prep_def_merge                        true
% 15.67/2.48  --prep_def_merge_prop_impl              false
% 15.67/2.48  --prep_def_merge_mbd                    true
% 15.67/2.48  --prep_def_merge_tr_red                 false
% 15.67/2.48  --prep_def_merge_tr_cl                  false
% 15.67/2.48  --smt_preprocessing                     true
% 15.67/2.48  --smt_ac_axioms                         fast
% 15.67/2.48  --preprocessed_out                      false
% 15.67/2.48  --preprocessed_stats                    false
% 15.67/2.48  
% 15.67/2.48  ------ Abstraction refinement Options
% 15.67/2.48  
% 15.67/2.48  --abstr_ref                             []
% 15.67/2.48  --abstr_ref_prep                        false
% 15.67/2.48  --abstr_ref_until_sat                   false
% 15.67/2.48  --abstr_ref_sig_restrict                funpre
% 15.67/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.67/2.48  --abstr_ref_under                       []
% 15.67/2.48  
% 15.67/2.48  ------ SAT Options
% 15.67/2.48  
% 15.67/2.48  --sat_mode                              false
% 15.67/2.48  --sat_fm_restart_options                ""
% 15.67/2.48  --sat_gr_def                            false
% 15.67/2.48  --sat_epr_types                         true
% 15.67/2.48  --sat_non_cyclic_types                  false
% 15.67/2.48  --sat_finite_models                     false
% 15.67/2.48  --sat_fm_lemmas                         false
% 15.67/2.48  --sat_fm_prep                           false
% 15.67/2.48  --sat_fm_uc_incr                        true
% 15.67/2.48  --sat_out_model                         small
% 15.67/2.48  --sat_out_clauses                       false
% 15.67/2.48  
% 15.67/2.48  ------ QBF Options
% 15.67/2.48  
% 15.67/2.48  --qbf_mode                              false
% 15.67/2.48  --qbf_elim_univ                         false
% 15.67/2.48  --qbf_dom_inst                          none
% 15.67/2.48  --qbf_dom_pre_inst                      false
% 15.67/2.48  --qbf_sk_in                             false
% 15.67/2.48  --qbf_pred_elim                         true
% 15.67/2.48  --qbf_split                             512
% 15.67/2.48  
% 15.67/2.48  ------ BMC1 Options
% 15.67/2.48  
% 15.67/2.48  --bmc1_incremental                      false
% 15.67/2.48  --bmc1_axioms                           reachable_all
% 15.67/2.48  --bmc1_min_bound                        0
% 15.67/2.48  --bmc1_max_bound                        -1
% 15.67/2.48  --bmc1_max_bound_default                -1
% 15.67/2.48  --bmc1_symbol_reachability              true
% 15.67/2.48  --bmc1_property_lemmas                  false
% 15.67/2.48  --bmc1_k_induction                      false
% 15.67/2.48  --bmc1_non_equiv_states                 false
% 15.67/2.48  --bmc1_deadlock                         false
% 15.67/2.48  --bmc1_ucm                              false
% 15.67/2.48  --bmc1_add_unsat_core                   none
% 15.67/2.48  --bmc1_unsat_core_children              false
% 15.67/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.67/2.48  --bmc1_out_stat                         full
% 15.67/2.48  --bmc1_ground_init                      false
% 15.67/2.48  --bmc1_pre_inst_next_state              false
% 15.67/2.48  --bmc1_pre_inst_state                   false
% 15.67/2.48  --bmc1_pre_inst_reach_state             false
% 15.67/2.48  --bmc1_out_unsat_core                   false
% 15.67/2.48  --bmc1_aig_witness_out                  false
% 15.67/2.48  --bmc1_verbose                          false
% 15.67/2.48  --bmc1_dump_clauses_tptp                false
% 15.67/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.67/2.48  --bmc1_dump_file                        -
% 15.67/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.67/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.67/2.48  --bmc1_ucm_extend_mode                  1
% 15.67/2.48  --bmc1_ucm_init_mode                    2
% 15.67/2.48  --bmc1_ucm_cone_mode                    none
% 15.67/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.67/2.48  --bmc1_ucm_relax_model                  4
% 15.67/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.67/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.67/2.48  --bmc1_ucm_layered_model                none
% 15.67/2.48  --bmc1_ucm_max_lemma_size               10
% 15.67/2.48  
% 15.67/2.48  ------ AIG Options
% 15.67/2.48  
% 15.67/2.48  --aig_mode                              false
% 15.67/2.48  
% 15.67/2.48  ------ Instantiation Options
% 15.67/2.48  
% 15.67/2.48  --instantiation_flag                    true
% 15.67/2.48  --inst_sos_flag                         false
% 15.67/2.48  --inst_sos_phase                        true
% 15.67/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.67/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.67/2.48  --inst_lit_sel_side                     none
% 15.67/2.48  --inst_solver_per_active                1400
% 15.67/2.48  --inst_solver_calls_frac                1.
% 15.67/2.48  --inst_passive_queue_type               priority_queues
% 15.67/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.67/2.48  --inst_passive_queues_freq              [25;2]
% 15.67/2.48  --inst_dismatching                      true
% 15.67/2.48  --inst_eager_unprocessed_to_passive     true
% 15.67/2.48  --inst_prop_sim_given                   true
% 15.67/2.48  --inst_prop_sim_new                     false
% 15.67/2.48  --inst_subs_new                         false
% 15.67/2.48  --inst_eq_res_simp                      false
% 15.67/2.48  --inst_subs_given                       false
% 15.67/2.48  --inst_orphan_elimination               true
% 15.67/2.48  --inst_learning_loop_flag               true
% 15.67/2.48  --inst_learning_start                   3000
% 15.67/2.48  --inst_learning_factor                  2
% 15.67/2.48  --inst_start_prop_sim_after_learn       3
% 15.67/2.48  --inst_sel_renew                        solver
% 15.67/2.48  --inst_lit_activity_flag                true
% 15.67/2.48  --inst_restr_to_given                   false
% 15.67/2.48  --inst_activity_threshold               500
% 15.67/2.48  --inst_out_proof                        true
% 15.67/2.48  
% 15.67/2.48  ------ Resolution Options
% 15.67/2.48  
% 15.67/2.48  --resolution_flag                       false
% 15.67/2.48  --res_lit_sel                           adaptive
% 15.67/2.48  --res_lit_sel_side                      none
% 15.67/2.48  --res_ordering                          kbo
% 15.67/2.48  --res_to_prop_solver                    active
% 15.67/2.48  --res_prop_simpl_new                    false
% 15.67/2.48  --res_prop_simpl_given                  true
% 15.67/2.48  --res_passive_queue_type                priority_queues
% 15.67/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.67/2.48  --res_passive_queues_freq               [15;5]
% 15.67/2.48  --res_forward_subs                      full
% 15.67/2.48  --res_backward_subs                     full
% 15.67/2.48  --res_forward_subs_resolution           true
% 15.67/2.48  --res_backward_subs_resolution          true
% 15.67/2.48  --res_orphan_elimination                true
% 15.67/2.48  --res_time_limit                        2.
% 15.67/2.48  --res_out_proof                         true
% 15.67/2.48  
% 15.67/2.48  ------ Superposition Options
% 15.67/2.48  
% 15.67/2.48  --superposition_flag                    true
% 15.67/2.48  --sup_passive_queue_type                priority_queues
% 15.67/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.67/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.67/2.48  --demod_completeness_check              fast
% 15.67/2.48  --demod_use_ground                      true
% 15.67/2.48  --sup_to_prop_solver                    passive
% 15.67/2.48  --sup_prop_simpl_new                    true
% 15.67/2.48  --sup_prop_simpl_given                  true
% 15.67/2.48  --sup_fun_splitting                     false
% 15.67/2.48  --sup_smt_interval                      50000
% 15.67/2.48  
% 15.67/2.48  ------ Superposition Simplification Setup
% 15.67/2.48  
% 15.67/2.48  --sup_indices_passive                   []
% 15.67/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.67/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.67/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.48  --sup_full_bw                           [BwDemod]
% 15.67/2.48  --sup_immed_triv                        [TrivRules]
% 15.67/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.67/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.48  --sup_immed_bw_main                     []
% 15.67/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.67/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.67/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.67/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.67/2.48  
% 15.67/2.48  ------ Combination Options
% 15.67/2.48  
% 15.67/2.48  --comb_res_mult                         3
% 15.67/2.48  --comb_sup_mult                         2
% 15.67/2.48  --comb_inst_mult                        10
% 15.67/2.48  
% 15.67/2.48  ------ Debug Options
% 15.67/2.48  
% 15.67/2.48  --dbg_backtrace                         false
% 15.67/2.48  --dbg_dump_prop_clauses                 false
% 15.67/2.48  --dbg_dump_prop_clauses_file            -
% 15.67/2.48  --dbg_out_stat                          false
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  ------ Proving...
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  % SZS status Theorem for theBenchmark.p
% 15.67/2.48  
% 15.67/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.67/2.48  
% 15.67/2.48  fof(f1,axiom,(
% 15.67/2.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f14,plain,(
% 15.67/2.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.67/2.48    inference(ennf_transformation,[],[f1])).
% 15.67/2.48  
% 15.67/2.48  fof(f32,plain,(
% 15.67/2.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f14])).
% 15.67/2.48  
% 15.67/2.48  fof(f4,axiom,(
% 15.67/2.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f17,plain,(
% 15.67/2.48    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 15.67/2.48    inference(ennf_transformation,[],[f4])).
% 15.67/2.48  
% 15.67/2.48  fof(f35,plain,(
% 15.67/2.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f17])).
% 15.67/2.48  
% 15.67/2.48  fof(f11,conjecture,(
% 15.67/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f12,negated_conjecture,(
% 15.67/2.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 15.67/2.48    inference(negated_conjecture,[],[f11])).
% 15.67/2.48  
% 15.67/2.48  fof(f13,plain,(
% 15.67/2.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 15.67/2.48    inference(pure_predicate_removal,[],[f12])).
% 15.67/2.48  
% 15.67/2.48  fof(f27,plain,(
% 15.67/2.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.67/2.48    inference(ennf_transformation,[],[f13])).
% 15.67/2.48  
% 15.67/2.48  fof(f30,plain,(
% 15.67/2.48    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.67/2.48    introduced(choice_axiom,[])).
% 15.67/2.48  
% 15.67/2.48  fof(f29,plain,(
% 15.67/2.48    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.67/2.48    introduced(choice_axiom,[])).
% 15.67/2.48  
% 15.67/2.48  fof(f28,plain,(
% 15.67/2.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 15.67/2.48    introduced(choice_axiom,[])).
% 15.67/2.48  
% 15.67/2.48  fof(f31,plain,(
% 15.67/2.48    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 15.67/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).
% 15.67/2.48  
% 15.67/2.48  fof(f43,plain,(
% 15.67/2.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.67/2.48    inference(cnf_transformation,[],[f31])).
% 15.67/2.48  
% 15.67/2.48  fof(f7,axiom,(
% 15.67/2.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f21,plain,(
% 15.67/2.48    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.67/2.48    inference(ennf_transformation,[],[f7])).
% 15.67/2.48  
% 15.67/2.48  fof(f38,plain,(
% 15.67/2.48    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.67/2.48    inference(cnf_transformation,[],[f21])).
% 15.67/2.48  
% 15.67/2.48  fof(f6,axiom,(
% 15.67/2.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f20,plain,(
% 15.67/2.48    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.67/2.48    inference(ennf_transformation,[],[f6])).
% 15.67/2.48  
% 15.67/2.48  fof(f37,plain,(
% 15.67/2.48    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.67/2.48    inference(cnf_transformation,[],[f20])).
% 15.67/2.48  
% 15.67/2.48  fof(f9,axiom,(
% 15.67/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f24,plain,(
% 15.67/2.48    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.67/2.48    inference(ennf_transformation,[],[f9])).
% 15.67/2.48  
% 15.67/2.48  fof(f40,plain,(
% 15.67/2.48    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f24])).
% 15.67/2.48  
% 15.67/2.48  fof(f42,plain,(
% 15.67/2.48    l1_pre_topc(sK0)),
% 15.67/2.48    inference(cnf_transformation,[],[f31])).
% 15.67/2.48  
% 15.67/2.48  fof(f3,axiom,(
% 15.67/2.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f15,plain,(
% 15.67/2.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 15.67/2.48    inference(ennf_transformation,[],[f3])).
% 15.67/2.48  
% 15.67/2.48  fof(f16,plain,(
% 15.67/2.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 15.67/2.48    inference(flattening,[],[f15])).
% 15.67/2.48  
% 15.67/2.48  fof(f34,plain,(
% 15.67/2.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f16])).
% 15.67/2.48  
% 15.67/2.48  fof(f10,axiom,(
% 15.67/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f25,plain,(
% 15.67/2.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.67/2.48    inference(ennf_transformation,[],[f10])).
% 15.67/2.48  
% 15.67/2.48  fof(f26,plain,(
% 15.67/2.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.67/2.48    inference(flattening,[],[f25])).
% 15.67/2.48  
% 15.67/2.48  fof(f41,plain,(
% 15.67/2.48    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f26])).
% 15.67/2.48  
% 15.67/2.48  fof(f5,axiom,(
% 15.67/2.48    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f18,plain,(
% 15.67/2.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 15.67/2.48    inference(ennf_transformation,[],[f5])).
% 15.67/2.48  
% 15.67/2.48  fof(f19,plain,(
% 15.67/2.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 15.67/2.48    inference(flattening,[],[f18])).
% 15.67/2.48  
% 15.67/2.48  fof(f36,plain,(
% 15.67/2.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f19])).
% 15.67/2.48  
% 15.67/2.48  fof(f8,axiom,(
% 15.67/2.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f22,plain,(
% 15.67/2.48    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.67/2.48    inference(ennf_transformation,[],[f8])).
% 15.67/2.48  
% 15.67/2.48  fof(f23,plain,(
% 15.67/2.48    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.67/2.48    inference(flattening,[],[f22])).
% 15.67/2.48  
% 15.67/2.48  fof(f39,plain,(
% 15.67/2.48    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f23])).
% 15.67/2.48  
% 15.67/2.48  fof(f45,plain,(
% 15.67/2.48    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 15.67/2.48    inference(cnf_transformation,[],[f31])).
% 15.67/2.48  
% 15.67/2.48  fof(f2,axiom,(
% 15.67/2.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f33,plain,(
% 15.67/2.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f2])).
% 15.67/2.48  
% 15.67/2.48  fof(f44,plain,(
% 15.67/2.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.67/2.48    inference(cnf_transformation,[],[f31])).
% 15.67/2.48  
% 15.67/2.48  cnf(c_0,plain,
% 15.67/2.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.67/2.48      inference(cnf_transformation,[],[f32]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_316,plain,
% 15.67/2.48      ( ~ r1_xboole_0(X0_40,X1_40) | r1_xboole_0(X1_40,X0_40) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_0]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_857,plain,
% 15.67/2.48      ( ~ r1_xboole_0(k1_tops_1(sK0,X0_40),k4_xboole_0(X1_40,X0_40))
% 15.67/2.48      | r1_xboole_0(k4_xboole_0(X1_40,X0_40),k1_tops_1(sK0,X0_40)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_316]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_54575,plain,
% 15.67/2.48      ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(X0_40,sK2))
% 15.67/2.48      | r1_xboole_0(k4_xboole_0(X0_40,sK2),k1_tops_1(sK0,sK2)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_857]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_54579,plain,
% 15.67/2.48      ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))
% 15.67/2.48      | r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_54575]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_3,plain,
% 15.67/2.48      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 15.67/2.48      inference(cnf_transformation,[],[f35]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_313,plain,
% 15.67/2.48      ( ~ r1_tarski(X0_40,X1_40)
% 15.67/2.48      | r1_xboole_0(X0_40,k4_xboole_0(X2_40,X1_40)) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_3]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_685,plain,
% 15.67/2.48      ( ~ r1_tarski(k1_tops_1(sK0,X0_40),X0_40)
% 15.67/2.48      | r1_xboole_0(k1_tops_1(sK0,X0_40),k4_xboole_0(X1_40,X0_40)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_313]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_33141,plain,
% 15.67/2.48      ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 15.67/2.48      | r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_685]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_12,negated_conjecture,
% 15.67/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.67/2.48      inference(cnf_transformation,[],[f43]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_307,negated_conjecture,
% 15.67/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_12]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_590,plain,
% 15.67/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_6,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.67/2.48      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 15.67/2.48      inference(cnf_transformation,[],[f38]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_310,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
% 15.67/2.48      | k7_subset_1(X0_42,X0_40,X1_40) = k4_xboole_0(X0_40,X1_40) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_6]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_587,plain,
% 15.67/2.48      ( k7_subset_1(X0_42,X0_40,X1_40) = k4_xboole_0(X0_40,X1_40)
% 15.67/2.48      | m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1095,plain,
% 15.67/2.48      ( k7_subset_1(u1_struct_0(sK0),sK1,X0_40) = k4_xboole_0(sK1,X0_40) ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_590,c_587]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_5,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.67/2.48      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 15.67/2.48      inference(cnf_transformation,[],[f37]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_311,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
% 15.67/2.48      | m1_subset_1(k7_subset_1(X0_42,X0_40,X1_40),k1_zfmisc_1(X0_42)) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_5]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_586,plain,
% 15.67/2.48      ( m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top
% 15.67/2.48      | m1_subset_1(k7_subset_1(X0_42,X0_40,X1_40),k1_zfmisc_1(X0_42)) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1348,plain,
% 15.67/2.48      ( m1_subset_1(k4_xboole_0(sK1,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 15.67/2.48      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_1095,c_586]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_15,plain,
% 15.67/2.48      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1669,plain,
% 15.67/2.48      ( m1_subset_1(k4_xboole_0(sK1,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.67/2.48      inference(global_propositional_subsumption,
% 15.67/2.48                [status(thm)],
% 15.67/2.48                [c_1348,c_15]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_8,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.67/2.48      | r1_tarski(k1_tops_1(X1,X0),X0)
% 15.67/2.48      | ~ l1_pre_topc(X1) ),
% 15.67/2.48      inference(cnf_transformation,[],[f40]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_13,negated_conjecture,
% 15.67/2.48      ( l1_pre_topc(sK0) ),
% 15.67/2.48      inference(cnf_transformation,[],[f42]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_175,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.67/2.48      | r1_tarski(k1_tops_1(X1,X0),X0)
% 15.67/2.48      | sK0 != X1 ),
% 15.67/2.48      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_176,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.67/2.48      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 15.67/2.48      inference(unflattening,[status(thm)],[c_175]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_305,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.67/2.48      | r1_tarski(k1_tops_1(sK0,X0_40),X0_40) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_176]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_592,plain,
% 15.67/2.48      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.67/2.48      | r1_tarski(k1_tops_1(sK0,X0_40),X0_40) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1676,plain,
% 15.67/2.48      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0_40)),k4_xboole_0(sK1,X0_40)) = iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_1669,c_592]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_2,plain,
% 15.67/2.48      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 15.67/2.48      inference(cnf_transformation,[],[f34]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_314,plain,
% 15.67/2.48      ( ~ r1_tarski(X0_40,X1_40)
% 15.67/2.48      | ~ r1_xboole_0(X1_40,X2_40)
% 15.67/2.48      | r1_xboole_0(X0_40,X2_40) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_2]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_583,plain,
% 15.67/2.48      ( r1_tarski(X0_40,X1_40) != iProver_top
% 15.67/2.48      | r1_xboole_0(X1_40,X2_40) != iProver_top
% 15.67/2.48      | r1_xboole_0(X0_40,X2_40) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1853,plain,
% 15.67/2.48      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0_40)),X1_40) = iProver_top
% 15.67/2.48      | r1_xboole_0(k4_xboole_0(sK1,X0_40),X1_40) != iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_1676,c_583]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_9,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.67/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.67/2.48      | ~ r1_tarski(X0,X2)
% 15.67/2.48      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 15.67/2.48      | ~ l1_pre_topc(X1) ),
% 15.67/2.48      inference(cnf_transformation,[],[f41]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_157,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.67/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.67/2.48      | ~ r1_tarski(X0,X2)
% 15.67/2.48      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 15.67/2.48      | sK0 != X1 ),
% 15.67/2.48      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_158,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.67/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.67/2.48      | ~ r1_tarski(X1,X0)
% 15.67/2.48      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 15.67/2.48      inference(unflattening,[status(thm)],[c_157]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_306,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.67/2.48      | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.67/2.48      | ~ r1_tarski(X1_40,X0_40)
% 15.67/2.48      | r1_tarski(k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_158]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_591,plain,
% 15.67/2.48      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.67/2.48      | m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.67/2.48      | r1_tarski(X1_40,X0_40) != iProver_top
% 15.67/2.48      | r1_tarski(k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_4,plain,
% 15.67/2.48      ( ~ r1_tarski(X0,X1)
% 15.67/2.48      | r1_tarski(X0,k4_xboole_0(X1,X2))
% 15.67/2.48      | ~ r1_xboole_0(X0,X2) ),
% 15.67/2.48      inference(cnf_transformation,[],[f36]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_312,plain,
% 15.67/2.48      ( ~ r1_tarski(X0_40,X1_40)
% 15.67/2.48      | r1_tarski(X0_40,k4_xboole_0(X1_40,X2_40))
% 15.67/2.48      | ~ r1_xboole_0(X0_40,X2_40) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_4]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_585,plain,
% 15.67/2.48      ( r1_tarski(X0_40,X1_40) != iProver_top
% 15.67/2.48      | r1_tarski(X0_40,k4_xboole_0(X1_40,X2_40)) = iProver_top
% 15.67/2.48      | r1_xboole_0(X0_40,X2_40) != iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_7,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.67/2.48      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.67/2.48      | ~ l1_pre_topc(X1) ),
% 15.67/2.48      inference(cnf_transformation,[],[f39]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_187,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.67/2.48      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.67/2.48      | sK0 != X1 ),
% 15.67/2.48      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_188,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.67/2.48      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.67/2.48      inference(unflattening,[status(thm)],[c_187]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_304,plain,
% 15.67/2.48      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.67/2.48      | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_188]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_593,plain,
% 15.67/2.48      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.67/2.48      | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1096,plain,
% 15.67/2.48      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_40),X1_40) = k4_xboole_0(k1_tops_1(sK0,X0_40),X1_40)
% 15.67/2.48      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_593,c_587]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_2748,plain,
% 15.67/2.48      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0_40) = k4_xboole_0(k1_tops_1(sK0,sK1),X0_40) ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_590,c_1096]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_10,negated_conjecture,
% 15.67/2.48      ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 15.67/2.48      inference(cnf_transformation,[],[f45]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_309,negated_conjecture,
% 15.67/2.48      ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_10]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_588,plain,
% 15.67/2.48      ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1346,plain,
% 15.67/2.48      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 15.67/2.48      inference(demodulation,[status(thm)],[c_1095,c_588]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_2868,plain,
% 15.67/2.48      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 15.67/2.48      inference(demodulation,[status(thm)],[c_2748,c_1346]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_2876,plain,
% 15.67/2.48      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top
% 15.67/2.48      | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_585,c_2868]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_12880,plain,
% 15.67/2.48      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.67/2.48      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.67/2.48      | r1_tarski(k4_xboole_0(sK1,sK2),sK1) != iProver_top
% 15.67/2.48      | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_591,c_2876]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1,plain,
% 15.67/2.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 15.67/2.48      inference(cnf_transformation,[],[f33]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_315,plain,
% 15.67/2.48      ( r1_tarski(k4_xboole_0(X0_40,X1_40),X0_40) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_1]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_14222,plain,
% 15.67/2.48      ( r1_tarski(k4_xboole_0(X0_40,sK2),X0_40) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_315]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_14223,plain,
% 15.67/2.48      ( r1_tarski(k4_xboole_0(X0_40,sK2),X0_40) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_14222]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_14225,plain,
% 15.67/2.48      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) = iProver_top ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_14223]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_24930,plain,
% 15.67/2.48      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.67/2.48      | r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
% 15.67/2.48      inference(global_propositional_subsumption,
% 15.67/2.48                [status(thm)],
% 15.67/2.48                [c_12880,c_15,c_14225]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_24936,plain,
% 15.67/2.48      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top ),
% 15.67/2.48      inference(forward_subsumption_resolution,
% 15.67/2.48                [status(thm)],
% 15.67/2.48                [c_24930,c_1669]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_24940,plain,
% 15.67/2.48      ( r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) != iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_1853,c_24936]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_24969,plain,
% 15.67/2.48      ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) ),
% 15.67/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_24940]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_11,negated_conjecture,
% 15.67/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.67/2.48      inference(cnf_transformation,[],[f44]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_308,negated_conjecture,
% 15.67/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.67/2.48      inference(subtyping,[status(esa)],[c_11]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_589,plain,
% 15.67/2.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_773,plain,
% 15.67/2.48      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_589,c_592]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_779,plain,
% 15.67/2.48      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 15.67/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_773]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(contradiction,plain,
% 15.67/2.48      ( $false ),
% 15.67/2.48      inference(minisat,[status(thm)],[c_54579,c_33141,c_24969,c_779]) ).
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.67/2.48  
% 15.67/2.48  ------                               Statistics
% 15.67/2.48  
% 15.67/2.48  ------ General
% 15.67/2.48  
% 15.67/2.48  abstr_ref_over_cycles:                  0
% 15.67/2.48  abstr_ref_under_cycles:                 0
% 15.67/2.48  gc_basic_clause_elim:                   0
% 15.67/2.48  forced_gc_time:                         0
% 15.67/2.48  parsing_time:                           0.008
% 15.67/2.48  unif_index_cands_time:                  0.
% 15.67/2.48  unif_index_add_time:                    0.
% 15.67/2.48  orderings_time:                         0.
% 15.67/2.48  out_proof_time:                         0.011
% 15.67/2.48  total_time:                             1.557
% 15.67/2.48  num_of_symbols:                         47
% 15.67/2.48  num_of_terms:                           67057
% 15.67/2.48  
% 15.67/2.48  ------ Preprocessing
% 15.67/2.48  
% 15.67/2.48  num_of_splits:                          0
% 15.67/2.48  num_of_split_atoms:                     0
% 15.67/2.48  num_of_reused_defs:                     0
% 15.67/2.48  num_eq_ax_congr_red:                    14
% 15.67/2.48  num_of_sem_filtered_clauses:            1
% 15.67/2.48  num_of_subtypes:                        4
% 15.67/2.48  monotx_restored_types:                  0
% 15.67/2.48  sat_num_of_epr_types:                   0
% 15.67/2.48  sat_num_of_non_cyclic_types:            0
% 15.67/2.48  sat_guarded_non_collapsed_types:        0
% 15.67/2.48  num_pure_diseq_elim:                    0
% 15.67/2.48  simp_replaced_by:                       0
% 15.67/2.48  res_preprocessed:                       68
% 15.67/2.48  prep_upred:                             0
% 15.67/2.48  prep_unflattend:                        3
% 15.67/2.48  smt_new_axioms:                         0
% 15.67/2.48  pred_elim_cands:                        3
% 15.67/2.48  pred_elim:                              1
% 15.67/2.48  pred_elim_cl:                           1
% 15.67/2.48  pred_elim_cycles:                       3
% 15.67/2.48  merged_defs:                            0
% 15.67/2.48  merged_defs_ncl:                        0
% 15.67/2.48  bin_hyper_res:                          0
% 15.67/2.48  prep_cycles:                            4
% 15.67/2.48  pred_elim_time:                         0.001
% 15.67/2.48  splitting_time:                         0.
% 15.67/2.48  sem_filter_time:                        0.
% 15.67/2.48  monotx_time:                            0.
% 15.67/2.48  subtype_inf_time:                       0.
% 15.67/2.48  
% 15.67/2.48  ------ Problem properties
% 15.67/2.48  
% 15.67/2.48  clauses:                                13
% 15.67/2.48  conjectures:                            3
% 15.67/2.48  epr:                                    2
% 15.67/2.48  horn:                                   13
% 15.67/2.48  ground:                                 3
% 15.67/2.48  unary:                                  4
% 15.67/2.48  binary:                                 6
% 15.67/2.48  lits:                                   26
% 15.67/2.48  lits_eq:                                1
% 15.67/2.48  fd_pure:                                0
% 15.67/2.48  fd_pseudo:                              0
% 15.67/2.48  fd_cond:                                0
% 15.67/2.48  fd_pseudo_cond:                         0
% 15.67/2.48  ac_symbols:                             0
% 15.67/2.48  
% 15.67/2.48  ------ Propositional Solver
% 15.67/2.48  
% 15.67/2.48  prop_solver_calls:                      32
% 15.67/2.48  prop_fast_solver_calls:                 1046
% 15.67/2.48  smt_solver_calls:                       0
% 15.67/2.48  smt_fast_solver_calls:                  0
% 15.67/2.48  prop_num_of_clauses:                    21175
% 15.67/2.48  prop_preprocess_simplified:             34291
% 15.67/2.48  prop_fo_subsumed:                       25
% 15.67/2.48  prop_solver_time:                       0.
% 15.67/2.48  smt_solver_time:                        0.
% 15.67/2.48  smt_fast_solver_time:                   0.
% 15.67/2.48  prop_fast_solver_time:                  0.
% 15.67/2.48  prop_unsat_core_time:                   0.002
% 15.67/2.48  
% 15.67/2.48  ------ QBF
% 15.67/2.48  
% 15.67/2.48  qbf_q_res:                              0
% 15.67/2.48  qbf_num_tautologies:                    0
% 15.67/2.48  qbf_prep_cycles:                        0
% 15.67/2.48  
% 15.67/2.48  ------ BMC1
% 15.67/2.48  
% 15.67/2.48  bmc1_current_bound:                     -1
% 15.67/2.48  bmc1_last_solved_bound:                 -1
% 15.67/2.48  bmc1_unsat_core_size:                   -1
% 15.67/2.48  bmc1_unsat_core_parents_size:           -1
% 15.67/2.48  bmc1_merge_next_fun:                    0
% 15.67/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.67/2.48  
% 15.67/2.48  ------ Instantiation
% 15.67/2.48  
% 15.67/2.48  inst_num_of_clauses:                    4502
% 15.67/2.48  inst_num_in_passive:                    1678
% 15.67/2.48  inst_num_in_active:                     1357
% 15.67/2.48  inst_num_in_unprocessed:                1470
% 15.67/2.48  inst_num_of_loops:                      1530
% 15.67/2.48  inst_num_of_learning_restarts:          0
% 15.67/2.48  inst_num_moves_active_passive:          168
% 15.67/2.48  inst_lit_activity:                      0
% 15.67/2.48  inst_lit_activity_moves:                1
% 15.67/2.48  inst_num_tautologies:                   0
% 15.67/2.48  inst_num_prop_implied:                  0
% 15.67/2.48  inst_num_existing_simplified:           0
% 15.67/2.48  inst_num_eq_res_simplified:             0
% 15.67/2.48  inst_num_child_elim:                    0
% 15.67/2.48  inst_num_of_dismatching_blockings:      8086
% 15.67/2.48  inst_num_of_non_proper_insts:           6463
% 15.67/2.48  inst_num_of_duplicates:                 0
% 15.67/2.48  inst_inst_num_from_inst_to_res:         0
% 15.67/2.48  inst_dismatching_checking_time:         0.
% 15.67/2.48  
% 15.67/2.48  ------ Resolution
% 15.67/2.48  
% 15.67/2.48  res_num_of_clauses:                     0
% 15.67/2.48  res_num_in_passive:                     0
% 15.67/2.48  res_num_in_active:                      0
% 15.67/2.48  res_num_of_loops:                       72
% 15.67/2.48  res_forward_subset_subsumed:            118
% 15.67/2.48  res_backward_subset_subsumed:           12
% 15.67/2.48  res_forward_subsumed:                   0
% 15.67/2.48  res_backward_subsumed:                  0
% 15.67/2.48  res_forward_subsumption_resolution:     0
% 15.67/2.48  res_backward_subsumption_resolution:    0
% 15.67/2.48  res_clause_to_clause_subsumption:       11497
% 15.67/2.48  res_orphan_elimination:                 0
% 15.67/2.48  res_tautology_del:                      412
% 15.67/2.48  res_num_eq_res_simplified:              0
% 15.67/2.48  res_num_sel_changes:                    0
% 15.67/2.48  res_moves_from_active_to_pass:          0
% 15.67/2.48  
% 15.67/2.48  ------ Superposition
% 15.67/2.48  
% 15.67/2.48  sup_time_total:                         0.
% 15.67/2.48  sup_time_generating:                    0.
% 15.67/2.48  sup_time_sim_full:                      0.
% 15.67/2.48  sup_time_sim_immed:                     0.
% 15.67/2.48  
% 15.67/2.48  sup_num_of_clauses:                     1741
% 15.67/2.48  sup_num_in_active:                      300
% 15.67/2.48  sup_num_in_passive:                     1441
% 15.67/2.48  sup_num_of_loops:                       304
% 15.67/2.48  sup_fw_superposition:                   980
% 15.67/2.48  sup_bw_superposition:                   1147
% 15.67/2.48  sup_immediate_simplified:               535
% 15.67/2.48  sup_given_eliminated:                   0
% 15.67/2.48  comparisons_done:                       0
% 15.67/2.48  comparisons_avoided:                    0
% 15.67/2.48  
% 15.67/2.48  ------ Simplifications
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  sim_fw_subset_subsumed:                 15
% 15.67/2.48  sim_bw_subset_subsumed:                 35
% 15.67/2.48  sim_fw_subsumed:                        102
% 15.67/2.48  sim_bw_subsumed:                        2
% 15.67/2.48  sim_fw_subsumption_res:                 2
% 15.67/2.48  sim_bw_subsumption_res:                 0
% 15.67/2.48  sim_tautology_del:                      2
% 15.67/2.48  sim_eq_tautology_del:                   6
% 15.67/2.48  sim_eq_res_simp:                        0
% 15.67/2.48  sim_fw_demodulated:                     53
% 15.67/2.48  sim_bw_demodulated:                     6
% 15.67/2.48  sim_light_normalised:                   409
% 15.67/2.48  sim_joinable_taut:                      0
% 15.67/2.48  sim_joinable_simp:                      0
% 15.67/2.48  sim_ac_normalised:                      0
% 15.67/2.48  sim_smt_subsumption:                    0
% 15.67/2.48  
%------------------------------------------------------------------------------
