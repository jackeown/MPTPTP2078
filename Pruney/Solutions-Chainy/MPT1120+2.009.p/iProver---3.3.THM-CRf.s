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
% DateTime   : Thu Dec  3 12:11:36 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 401 expanded)
%              Number of clauses        :  109 ( 179 expanded)
%              Number of leaves         :   16 (  98 expanded)
%              Depth                    :   21
%              Number of atoms          :  357 (1263 expanded)
%              Number of equality atoms :  114 ( 144 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23,f22])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
    | r1_tarski(X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1709,plain,
    ( ~ m1_subset_1(k3_xboole_0(X0_39,X1_39),k1_zfmisc_1(X2_39))
    | r1_tarski(k3_xboole_0(X0_39,X1_39),X2_39) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_6147,plain,
    ( ~ m1_subset_1(k3_xboole_0(X0_39,sK2),k1_zfmisc_1(X1_39))
    | r1_tarski(k3_xboole_0(X0_39,sK2),X1_39) ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_26760,plain,
    ( ~ m1_subset_1(k3_xboole_0(X0_39,sK2),k1_zfmisc_1(sK2))
    | r1_tarski(k3_xboole_0(X0_39,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_6147])).

cnf(c_26764,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))
    | r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_26760])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_166,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_167,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_166])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_39,X0_39)
    | r1_tarski(k2_pre_topc(sK0,X1_39),k2_pre_topc(sK0,X0_39)) ),
    inference(subtyping,[status(esa)],[c_167])).

cnf(c_1124,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(X1_39,X2_39),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X1_39,X2_39)),k2_pre_topc(sK0,X0_39))
    | ~ r1_tarski(k3_xboole_0(X1_39,X2_39),X0_39) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_16871,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,X0_39))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0_39) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_26007,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_16871])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_317,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X0_39,X2_39)
    | r1_tarski(X0_39,k3_xboole_0(X2_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_618,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(X0_39,X2_39) != iProver_top
    | r1_tarski(X0_39,k3_xboole_0(X1_39,X2_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_185,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_185])).

cnf(c_627,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_621,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) != iProver_top
    | r1_tarski(X0_39,X1_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_1108,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0_39),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_621])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_311,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_624,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_312,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_623,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_626,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_39,X0_39) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1_39),k2_pre_topc(sK0,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_316,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X1_39,X2_39)
    | r1_tarski(X0_39,X2_39) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_619,plain,
    ( r1_tarski(X0_39,X1_39) != iProver_top
    | r1_tarski(X1_39,X2_39) != iProver_top
    | r1_tarski(X0_39,X2_39) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1116,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_39,X0_39) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0_39),X2_39) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1_39),X2_39) = iProver_top ),
    inference(superposition,[status(thm)],[c_626,c_619])).

cnf(c_1410,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_39,sK2) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0_39),X1_39) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK2),X1_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_1116])).

cnf(c_1533,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),X0_39) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0_39) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_624,c_1410])).

cnf(c_1547,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1108,c_1533])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_360,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_362,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_723,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,X0_39),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_724,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0_39),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_726,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_2150,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1547,c_14,c_362,c_726])).

cnf(c_1411,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_39,sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0_39),X1_39) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X1_39) != iProver_top ),
    inference(superposition,[status(thm)],[c_624,c_1116])).

cnf(c_1633,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),X0_39) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0_39) != iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_1411])).

cnf(c_2156,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2150,c_1633])).

cnf(c_15,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1528,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_1529,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1528])).

cnf(c_2031,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_2032,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2031])).

cnf(c_2163,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2156,c_15,c_1529,c_2032])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_93,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_94,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_93])).

cnf(c_115,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_94])).

cnf(c_310,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | k9_subset_1(X1_39,X2_39,X0_39) = k3_xboole_0(X2_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_115])).

cnf(c_625,plain,
    ( k9_subset_1(X0_39,X1_39,X2_39) = k3_xboole_0(X1_39,X2_39)
    | r1_tarski(X2_39,X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_2168,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_39,k2_pre_topc(sK0,sK2)) = k3_xboole_0(X0_39,k2_pre_topc(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_2163,c_625])).

cnf(c_1106,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_621])).

cnf(c_1645,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_39,sK2) = k3_xboole_0(X0_39,sK2) ),
    inference(superposition,[status(thm)],[c_1106,c_625])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_313,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_622,plain,
    ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_1995,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1645,c_622])).

cnf(c_24797,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2168,c_1995])).

cnf(c_25185,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_618,c_24797])).

cnf(c_25186,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25185])).

cnf(c_322,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_19047,plain,
    ( k1_zfmisc_1(sK2) = k1_zfmisc_1(sK2) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_323,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_1060,plain,
    ( X0_39 != X1_39
    | X0_39 = k3_xboole_0(X2_39,X3_39)
    | k3_xboole_0(X2_39,X3_39) != X1_39 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_1847,plain,
    ( X0_39 != k3_xboole_0(X1_39,X2_39)
    | X0_39 = k3_xboole_0(X2_39,X1_39)
    | k3_xboole_0(X2_39,X1_39) != k3_xboole_0(X1_39,X2_39) ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_3813,plain,
    ( k3_xboole_0(X0_39,X1_39) != k3_xboole_0(X1_39,X0_39)
    | k3_xboole_0(X1_39,X0_39) != k3_xboole_0(X1_39,X0_39)
    | k3_xboole_0(X1_39,X0_39) = k3_xboole_0(X0_39,X1_39) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_15625,plain,
    ( k3_xboole_0(sK2,sK1) != k3_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1)
    | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3813])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(X0_39,X1_39),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X0_39,X1_39)),k2_pre_topc(sK0,X0_39))
    | ~ r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_14918,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_315,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
    | ~ r1_tarski(X0_39,X1_39) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_884,plain,
    ( m1_subset_1(k3_xboole_0(X0_39,X1_39),k1_zfmisc_1(X0_39))
    | ~ r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_12825,plain,
    ( m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(sK2))
    | ~ r1_tarski(k3_xboole_0(sK2,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_740,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(k3_xboole_0(X0_39,X2_39),X0_39)
    | r1_tarski(k3_xboole_0(X0_39,X2_39),X1_39) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_1146,plain,
    ( ~ r1_tarski(X0_39,u1_struct_0(sK0))
    | ~ r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39)
    | r1_tarski(k3_xboole_0(X0_39,X1_39),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_12813,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0_39,X0_40)
    | m1_subset_1(X1_39,X1_40)
    | X1_40 != X0_40
    | X1_39 != X0_39 ),
    theory(equality)).

cnf(c_1088,plain,
    ( m1_subset_1(X0_39,X0_40)
    | ~ m1_subset_1(k3_xboole_0(X1_39,X2_39),k1_zfmisc_1(X1_39))
    | X0_40 != k1_zfmisc_1(X1_39)
    | X0_39 != k3_xboole_0(X1_39,X2_39) ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_1759,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
    | ~ m1_subset_1(k3_xboole_0(X1_39,X2_39),k1_zfmisc_1(X1_39))
    | k1_zfmisc_1(X1_39) != k1_zfmisc_1(X1_39)
    | X0_39 != k3_xboole_0(X1_39,X2_39) ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_1938,plain,
    ( ~ m1_subset_1(k3_xboole_0(X0_39,X1_39),k1_zfmisc_1(X0_39))
    | m1_subset_1(k3_xboole_0(X1_39,X0_39),k1_zfmisc_1(X0_39))
    | k1_zfmisc_1(X0_39) != k1_zfmisc_1(X0_39)
    | k3_xboole_0(X1_39,X0_39) != k3_xboole_0(X0_39,X1_39) ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_6359,plain,
    ( m1_subset_1(k3_xboole_0(X0_39,sK2),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(k3_xboole_0(sK2,X0_39),k1_zfmisc_1(sK2))
    | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2)
    | k3_xboole_0(X0_39,sK2) != k3_xboole_0(sK2,X0_39) ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_6365,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(sK2))
    | m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))
    | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2)
    | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_6359])).

cnf(c_1,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_318,plain,
    ( r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6211,plain,
    ( r1_tarski(k3_xboole_0(X0_39,sK2),X0_39) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_6213,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_6211])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_319,plain,
    ( k3_xboole_0(X0_39,X1_39) = k3_xboole_0(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_5821,plain,
    ( k3_xboole_0(sK2,X0_39) = k3_xboole_0(X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_5822,plain,
    ( k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_5821])).

cnf(c_321,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_5816,plain,
    ( k3_xboole_0(X0_39,sK2) = k3_xboole_0(X0_39,sK2) ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_5817,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_5816])).

cnf(c_1329,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_39,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_5110,plain,
    ( m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_2238,plain,
    ( r1_tarski(k3_xboole_0(sK2,X0_39),sK2) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_2240,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_2238])).

cnf(c_720,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26764,c_26007,c_25186,c_19047,c_15625,c_14918,c_12825,c_12813,c_6365,c_6213,c_5822,c_5817,c_5110,c_2240,c_720,c_10,c_11])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.76/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.76/1.50  
% 7.76/1.50  ------  iProver source info
% 7.76/1.50  
% 7.76/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.76/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.76/1.50  git: non_committed_changes: false
% 7.76/1.50  git: last_make_outside_of_git: false
% 7.76/1.50  
% 7.76/1.50  ------ 
% 7.76/1.50  
% 7.76/1.50  ------ Input Options
% 7.76/1.50  
% 7.76/1.50  --out_options                           all
% 7.76/1.50  --tptp_safe_out                         true
% 7.76/1.50  --problem_path                          ""
% 7.76/1.50  --include_path                          ""
% 7.76/1.50  --clausifier                            res/vclausify_rel
% 7.76/1.50  --clausifier_options                    ""
% 7.76/1.50  --stdin                                 false
% 7.76/1.50  --stats_out                             all
% 7.76/1.50  
% 7.76/1.50  ------ General Options
% 7.76/1.50  
% 7.76/1.50  --fof                                   false
% 7.76/1.50  --time_out_real                         305.
% 7.76/1.50  --time_out_virtual                      -1.
% 7.76/1.50  --symbol_type_check                     false
% 7.76/1.50  --clausify_out                          false
% 7.76/1.50  --sig_cnt_out                           false
% 7.76/1.50  --trig_cnt_out                          false
% 7.76/1.50  --trig_cnt_out_tolerance                1.
% 7.76/1.50  --trig_cnt_out_sk_spl                   false
% 7.76/1.50  --abstr_cl_out                          false
% 7.76/1.50  
% 7.76/1.50  ------ Global Options
% 7.76/1.50  
% 7.76/1.50  --schedule                              default
% 7.76/1.50  --add_important_lit                     false
% 7.76/1.50  --prop_solver_per_cl                    1000
% 7.76/1.50  --min_unsat_core                        false
% 7.76/1.50  --soft_assumptions                      false
% 7.76/1.50  --soft_lemma_size                       3
% 7.76/1.50  --prop_impl_unit_size                   0
% 7.76/1.50  --prop_impl_unit                        []
% 7.76/1.50  --share_sel_clauses                     true
% 7.76/1.50  --reset_solvers                         false
% 7.76/1.50  --bc_imp_inh                            [conj_cone]
% 7.76/1.50  --conj_cone_tolerance                   3.
% 7.76/1.50  --extra_neg_conj                        none
% 7.76/1.50  --large_theory_mode                     true
% 7.76/1.50  --prolific_symb_bound                   200
% 7.76/1.50  --lt_threshold                          2000
% 7.76/1.50  --clause_weak_htbl                      true
% 7.76/1.50  --gc_record_bc_elim                     false
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing Options
% 7.76/1.50  
% 7.76/1.50  --preprocessing_flag                    true
% 7.76/1.50  --time_out_prep_mult                    0.1
% 7.76/1.50  --splitting_mode                        input
% 7.76/1.50  --splitting_grd                         true
% 7.76/1.50  --splitting_cvd                         false
% 7.76/1.50  --splitting_cvd_svl                     false
% 7.76/1.50  --splitting_nvd                         32
% 7.76/1.50  --sub_typing                            true
% 7.76/1.50  --prep_gs_sim                           true
% 7.76/1.50  --prep_unflatten                        true
% 7.76/1.50  --prep_res_sim                          true
% 7.76/1.50  --prep_upred                            true
% 7.76/1.50  --prep_sem_filter                       exhaustive
% 7.76/1.50  --prep_sem_filter_out                   false
% 7.76/1.50  --pred_elim                             true
% 7.76/1.50  --res_sim_input                         true
% 7.76/1.50  --eq_ax_congr_red                       true
% 7.76/1.50  --pure_diseq_elim                       true
% 7.76/1.50  --brand_transform                       false
% 7.76/1.50  --non_eq_to_eq                          false
% 7.76/1.50  --prep_def_merge                        true
% 7.76/1.50  --prep_def_merge_prop_impl              false
% 7.76/1.50  --prep_def_merge_mbd                    true
% 7.76/1.50  --prep_def_merge_tr_red                 false
% 7.76/1.50  --prep_def_merge_tr_cl                  false
% 7.76/1.50  --smt_preprocessing                     true
% 7.76/1.50  --smt_ac_axioms                         fast
% 7.76/1.50  --preprocessed_out                      false
% 7.76/1.50  --preprocessed_stats                    false
% 7.76/1.50  
% 7.76/1.50  ------ Abstraction refinement Options
% 7.76/1.50  
% 7.76/1.50  --abstr_ref                             []
% 7.76/1.50  --abstr_ref_prep                        false
% 7.76/1.50  --abstr_ref_until_sat                   false
% 7.76/1.50  --abstr_ref_sig_restrict                funpre
% 7.76/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.50  --abstr_ref_under                       []
% 7.76/1.50  
% 7.76/1.50  ------ SAT Options
% 7.76/1.50  
% 7.76/1.50  --sat_mode                              false
% 7.76/1.50  --sat_fm_restart_options                ""
% 7.76/1.50  --sat_gr_def                            false
% 7.76/1.50  --sat_epr_types                         true
% 7.76/1.50  --sat_non_cyclic_types                  false
% 7.76/1.50  --sat_finite_models                     false
% 7.76/1.50  --sat_fm_lemmas                         false
% 7.76/1.50  --sat_fm_prep                           false
% 7.76/1.50  --sat_fm_uc_incr                        true
% 7.76/1.50  --sat_out_model                         small
% 7.76/1.50  --sat_out_clauses                       false
% 7.76/1.50  
% 7.76/1.50  ------ QBF Options
% 7.76/1.50  
% 7.76/1.50  --qbf_mode                              false
% 7.76/1.50  --qbf_elim_univ                         false
% 7.76/1.50  --qbf_dom_inst                          none
% 7.76/1.50  --qbf_dom_pre_inst                      false
% 7.76/1.50  --qbf_sk_in                             false
% 7.76/1.50  --qbf_pred_elim                         true
% 7.76/1.50  --qbf_split                             512
% 7.76/1.50  
% 7.76/1.50  ------ BMC1 Options
% 7.76/1.50  
% 7.76/1.50  --bmc1_incremental                      false
% 7.76/1.50  --bmc1_axioms                           reachable_all
% 7.76/1.50  --bmc1_min_bound                        0
% 7.76/1.50  --bmc1_max_bound                        -1
% 7.76/1.50  --bmc1_max_bound_default                -1
% 7.76/1.50  --bmc1_symbol_reachability              true
% 7.76/1.50  --bmc1_property_lemmas                  false
% 7.76/1.50  --bmc1_k_induction                      false
% 7.76/1.50  --bmc1_non_equiv_states                 false
% 7.76/1.50  --bmc1_deadlock                         false
% 7.76/1.50  --bmc1_ucm                              false
% 7.76/1.50  --bmc1_add_unsat_core                   none
% 7.76/1.50  --bmc1_unsat_core_children              false
% 7.76/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.50  --bmc1_out_stat                         full
% 7.76/1.50  --bmc1_ground_init                      false
% 7.76/1.50  --bmc1_pre_inst_next_state              false
% 7.76/1.50  --bmc1_pre_inst_state                   false
% 7.76/1.50  --bmc1_pre_inst_reach_state             false
% 7.76/1.50  --bmc1_out_unsat_core                   false
% 7.76/1.50  --bmc1_aig_witness_out                  false
% 7.76/1.50  --bmc1_verbose                          false
% 7.76/1.50  --bmc1_dump_clauses_tptp                false
% 7.76/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.50  --bmc1_dump_file                        -
% 7.76/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.50  --bmc1_ucm_extend_mode                  1
% 7.76/1.50  --bmc1_ucm_init_mode                    2
% 7.76/1.50  --bmc1_ucm_cone_mode                    none
% 7.76/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.50  --bmc1_ucm_relax_model                  4
% 7.76/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.50  --bmc1_ucm_layered_model                none
% 7.76/1.50  --bmc1_ucm_max_lemma_size               10
% 7.76/1.50  
% 7.76/1.50  ------ AIG Options
% 7.76/1.50  
% 7.76/1.50  --aig_mode                              false
% 7.76/1.50  
% 7.76/1.50  ------ Instantiation Options
% 7.76/1.50  
% 7.76/1.50  --instantiation_flag                    true
% 7.76/1.50  --inst_sos_flag                         true
% 7.76/1.50  --inst_sos_phase                        true
% 7.76/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.50  --inst_lit_sel_side                     num_symb
% 7.76/1.50  --inst_solver_per_active                1400
% 7.76/1.50  --inst_solver_calls_frac                1.
% 7.76/1.50  --inst_passive_queue_type               priority_queues
% 7.76/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.50  --inst_passive_queues_freq              [25;2]
% 7.76/1.50  --inst_dismatching                      true
% 7.76/1.50  --inst_eager_unprocessed_to_passive     true
% 7.76/1.50  --inst_prop_sim_given                   true
% 7.76/1.50  --inst_prop_sim_new                     false
% 7.76/1.50  --inst_subs_new                         false
% 7.76/1.50  --inst_eq_res_simp                      false
% 7.76/1.50  --inst_subs_given                       false
% 7.76/1.50  --inst_orphan_elimination               true
% 7.76/1.50  --inst_learning_loop_flag               true
% 7.76/1.50  --inst_learning_start                   3000
% 7.76/1.50  --inst_learning_factor                  2
% 7.76/1.50  --inst_start_prop_sim_after_learn       3
% 7.76/1.50  --inst_sel_renew                        solver
% 7.76/1.50  --inst_lit_activity_flag                true
% 7.76/1.50  --inst_restr_to_given                   false
% 7.76/1.50  --inst_activity_threshold               500
% 7.76/1.50  --inst_out_proof                        true
% 7.76/1.50  
% 7.76/1.50  ------ Resolution Options
% 7.76/1.50  
% 7.76/1.50  --resolution_flag                       true
% 7.76/1.50  --res_lit_sel                           adaptive
% 7.76/1.50  --res_lit_sel_side                      none
% 7.76/1.50  --res_ordering                          kbo
% 7.76/1.50  --res_to_prop_solver                    active
% 7.76/1.50  --res_prop_simpl_new                    false
% 7.76/1.50  --res_prop_simpl_given                  true
% 7.76/1.50  --res_passive_queue_type                priority_queues
% 7.76/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.50  --res_passive_queues_freq               [15;5]
% 7.76/1.50  --res_forward_subs                      full
% 7.76/1.50  --res_backward_subs                     full
% 7.76/1.50  --res_forward_subs_resolution           true
% 7.76/1.50  --res_backward_subs_resolution          true
% 7.76/1.50  --res_orphan_elimination                true
% 7.76/1.50  --res_time_limit                        2.
% 7.76/1.50  --res_out_proof                         true
% 7.76/1.50  
% 7.76/1.50  ------ Superposition Options
% 7.76/1.50  
% 7.76/1.50  --superposition_flag                    true
% 7.76/1.50  --sup_passive_queue_type                priority_queues
% 7.76/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.76/1.50  --demod_completeness_check              fast
% 7.76/1.50  --demod_use_ground                      true
% 7.76/1.50  --sup_to_prop_solver                    passive
% 7.76/1.50  --sup_prop_simpl_new                    true
% 7.76/1.50  --sup_prop_simpl_given                  true
% 7.76/1.50  --sup_fun_splitting                     true
% 7.76/1.50  --sup_smt_interval                      50000
% 7.76/1.50  
% 7.76/1.50  ------ Superposition Simplification Setup
% 7.76/1.50  
% 7.76/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.76/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.76/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.76/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.76/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.76/1.50  --sup_immed_triv                        [TrivRules]
% 7.76/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_immed_bw_main                     []
% 7.76/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.76/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_input_bw                          []
% 7.76/1.50  
% 7.76/1.50  ------ Combination Options
% 7.76/1.50  
% 7.76/1.50  --comb_res_mult                         3
% 7.76/1.50  --comb_sup_mult                         2
% 7.76/1.50  --comb_inst_mult                        10
% 7.76/1.50  
% 7.76/1.50  ------ Debug Options
% 7.76/1.50  
% 7.76/1.50  --dbg_backtrace                         false
% 7.76/1.50  --dbg_dump_prop_clauses                 false
% 7.76/1.50  --dbg_dump_prop_clauses_file            -
% 7.76/1.50  --dbg_out_stat                          false
% 7.76/1.50  ------ Parsing...
% 7.76/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.50  ------ Proving...
% 7.76/1.50  ------ Problem Properties 
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  clauses                                 12
% 7.76/1.50  conjectures                             3
% 7.76/1.50  EPR                                     1
% 7.76/1.50  Horn                                    12
% 7.76/1.50  unary                                   5
% 7.76/1.50  binary                                  4
% 7.76/1.50  lits                                    23
% 7.76/1.50  lits eq                                 2
% 7.76/1.50  fd_pure                                 0
% 7.76/1.50  fd_pseudo                               0
% 7.76/1.50  fd_cond                                 0
% 7.76/1.50  fd_pseudo_cond                          0
% 7.76/1.50  AC symbols                              0
% 7.76/1.50  
% 7.76/1.50  ------ Schedule dynamic 5 is on 
% 7.76/1.50  
% 7.76/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ 
% 7.76/1.50  Current options:
% 7.76/1.50  ------ 
% 7.76/1.50  
% 7.76/1.50  ------ Input Options
% 7.76/1.50  
% 7.76/1.50  --out_options                           all
% 7.76/1.50  --tptp_safe_out                         true
% 7.76/1.50  --problem_path                          ""
% 7.76/1.50  --include_path                          ""
% 7.76/1.50  --clausifier                            res/vclausify_rel
% 7.76/1.50  --clausifier_options                    ""
% 7.76/1.50  --stdin                                 false
% 7.76/1.50  --stats_out                             all
% 7.76/1.50  
% 7.76/1.50  ------ General Options
% 7.76/1.50  
% 7.76/1.50  --fof                                   false
% 7.76/1.50  --time_out_real                         305.
% 7.76/1.50  --time_out_virtual                      -1.
% 7.76/1.50  --symbol_type_check                     false
% 7.76/1.50  --clausify_out                          false
% 7.76/1.50  --sig_cnt_out                           false
% 7.76/1.50  --trig_cnt_out                          false
% 7.76/1.50  --trig_cnt_out_tolerance                1.
% 7.76/1.50  --trig_cnt_out_sk_spl                   false
% 7.76/1.50  --abstr_cl_out                          false
% 7.76/1.50  
% 7.76/1.50  ------ Global Options
% 7.76/1.50  
% 7.76/1.50  --schedule                              default
% 7.76/1.50  --add_important_lit                     false
% 7.76/1.50  --prop_solver_per_cl                    1000
% 7.76/1.50  --min_unsat_core                        false
% 7.76/1.50  --soft_assumptions                      false
% 7.76/1.50  --soft_lemma_size                       3
% 7.76/1.50  --prop_impl_unit_size                   0
% 7.76/1.50  --prop_impl_unit                        []
% 7.76/1.50  --share_sel_clauses                     true
% 7.76/1.50  --reset_solvers                         false
% 7.76/1.50  --bc_imp_inh                            [conj_cone]
% 7.76/1.50  --conj_cone_tolerance                   3.
% 7.76/1.50  --extra_neg_conj                        none
% 7.76/1.50  --large_theory_mode                     true
% 7.76/1.50  --prolific_symb_bound                   200
% 7.76/1.50  --lt_threshold                          2000
% 7.76/1.50  --clause_weak_htbl                      true
% 7.76/1.50  --gc_record_bc_elim                     false
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing Options
% 7.76/1.50  
% 7.76/1.50  --preprocessing_flag                    true
% 7.76/1.50  --time_out_prep_mult                    0.1
% 7.76/1.50  --splitting_mode                        input
% 7.76/1.50  --splitting_grd                         true
% 7.76/1.50  --splitting_cvd                         false
% 7.76/1.50  --splitting_cvd_svl                     false
% 7.76/1.50  --splitting_nvd                         32
% 7.76/1.50  --sub_typing                            true
% 7.76/1.50  --prep_gs_sim                           true
% 7.76/1.50  --prep_unflatten                        true
% 7.76/1.50  --prep_res_sim                          true
% 7.76/1.50  --prep_upred                            true
% 7.76/1.50  --prep_sem_filter                       exhaustive
% 7.76/1.50  --prep_sem_filter_out                   false
% 7.76/1.50  --pred_elim                             true
% 7.76/1.50  --res_sim_input                         true
% 7.76/1.50  --eq_ax_congr_red                       true
% 7.76/1.50  --pure_diseq_elim                       true
% 7.76/1.50  --brand_transform                       false
% 7.76/1.50  --non_eq_to_eq                          false
% 7.76/1.50  --prep_def_merge                        true
% 7.76/1.50  --prep_def_merge_prop_impl              false
% 7.76/1.50  --prep_def_merge_mbd                    true
% 7.76/1.50  --prep_def_merge_tr_red                 false
% 7.76/1.50  --prep_def_merge_tr_cl                  false
% 7.76/1.50  --smt_preprocessing                     true
% 7.76/1.50  --smt_ac_axioms                         fast
% 7.76/1.50  --preprocessed_out                      false
% 7.76/1.50  --preprocessed_stats                    false
% 7.76/1.50  
% 7.76/1.50  ------ Abstraction refinement Options
% 7.76/1.50  
% 7.76/1.50  --abstr_ref                             []
% 7.76/1.50  --abstr_ref_prep                        false
% 7.76/1.50  --abstr_ref_until_sat                   false
% 7.76/1.50  --abstr_ref_sig_restrict                funpre
% 7.76/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.50  --abstr_ref_under                       []
% 7.76/1.50  
% 7.76/1.50  ------ SAT Options
% 7.76/1.50  
% 7.76/1.50  --sat_mode                              false
% 7.76/1.50  --sat_fm_restart_options                ""
% 7.76/1.50  --sat_gr_def                            false
% 7.76/1.50  --sat_epr_types                         true
% 7.76/1.50  --sat_non_cyclic_types                  false
% 7.76/1.50  --sat_finite_models                     false
% 7.76/1.50  --sat_fm_lemmas                         false
% 7.76/1.50  --sat_fm_prep                           false
% 7.76/1.50  --sat_fm_uc_incr                        true
% 7.76/1.50  --sat_out_model                         small
% 7.76/1.50  --sat_out_clauses                       false
% 7.76/1.50  
% 7.76/1.50  ------ QBF Options
% 7.76/1.50  
% 7.76/1.50  --qbf_mode                              false
% 7.76/1.50  --qbf_elim_univ                         false
% 7.76/1.50  --qbf_dom_inst                          none
% 7.76/1.50  --qbf_dom_pre_inst                      false
% 7.76/1.50  --qbf_sk_in                             false
% 7.76/1.50  --qbf_pred_elim                         true
% 7.76/1.50  --qbf_split                             512
% 7.76/1.50  
% 7.76/1.50  ------ BMC1 Options
% 7.76/1.50  
% 7.76/1.50  --bmc1_incremental                      false
% 7.76/1.50  --bmc1_axioms                           reachable_all
% 7.76/1.50  --bmc1_min_bound                        0
% 7.76/1.50  --bmc1_max_bound                        -1
% 7.76/1.50  --bmc1_max_bound_default                -1
% 7.76/1.50  --bmc1_symbol_reachability              true
% 7.76/1.50  --bmc1_property_lemmas                  false
% 7.76/1.50  --bmc1_k_induction                      false
% 7.76/1.50  --bmc1_non_equiv_states                 false
% 7.76/1.50  --bmc1_deadlock                         false
% 7.76/1.50  --bmc1_ucm                              false
% 7.76/1.50  --bmc1_add_unsat_core                   none
% 7.76/1.50  --bmc1_unsat_core_children              false
% 7.76/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.50  --bmc1_out_stat                         full
% 7.76/1.50  --bmc1_ground_init                      false
% 7.76/1.50  --bmc1_pre_inst_next_state              false
% 7.76/1.50  --bmc1_pre_inst_state                   false
% 7.76/1.50  --bmc1_pre_inst_reach_state             false
% 7.76/1.50  --bmc1_out_unsat_core                   false
% 7.76/1.50  --bmc1_aig_witness_out                  false
% 7.76/1.50  --bmc1_verbose                          false
% 7.76/1.50  --bmc1_dump_clauses_tptp                false
% 7.76/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.50  --bmc1_dump_file                        -
% 7.76/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.50  --bmc1_ucm_extend_mode                  1
% 7.76/1.50  --bmc1_ucm_init_mode                    2
% 7.76/1.50  --bmc1_ucm_cone_mode                    none
% 7.76/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.50  --bmc1_ucm_relax_model                  4
% 7.76/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.50  --bmc1_ucm_layered_model                none
% 7.76/1.50  --bmc1_ucm_max_lemma_size               10
% 7.76/1.50  
% 7.76/1.50  ------ AIG Options
% 7.76/1.50  
% 7.76/1.50  --aig_mode                              false
% 7.76/1.50  
% 7.76/1.50  ------ Instantiation Options
% 7.76/1.50  
% 7.76/1.50  --instantiation_flag                    true
% 7.76/1.50  --inst_sos_flag                         true
% 7.76/1.50  --inst_sos_phase                        true
% 7.76/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.50  --inst_lit_sel_side                     none
% 7.76/1.50  --inst_solver_per_active                1400
% 7.76/1.50  --inst_solver_calls_frac                1.
% 7.76/1.50  --inst_passive_queue_type               priority_queues
% 7.76/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.50  --inst_passive_queues_freq              [25;2]
% 7.76/1.50  --inst_dismatching                      true
% 7.76/1.50  --inst_eager_unprocessed_to_passive     true
% 7.76/1.50  --inst_prop_sim_given                   true
% 7.76/1.50  --inst_prop_sim_new                     false
% 7.76/1.50  --inst_subs_new                         false
% 7.76/1.50  --inst_eq_res_simp                      false
% 7.76/1.50  --inst_subs_given                       false
% 7.76/1.50  --inst_orphan_elimination               true
% 7.76/1.50  --inst_learning_loop_flag               true
% 7.76/1.50  --inst_learning_start                   3000
% 7.76/1.50  --inst_learning_factor                  2
% 7.76/1.50  --inst_start_prop_sim_after_learn       3
% 7.76/1.50  --inst_sel_renew                        solver
% 7.76/1.50  --inst_lit_activity_flag                true
% 7.76/1.50  --inst_restr_to_given                   false
% 7.76/1.50  --inst_activity_threshold               500
% 7.76/1.50  --inst_out_proof                        true
% 7.76/1.50  
% 7.76/1.50  ------ Resolution Options
% 7.76/1.50  
% 7.76/1.50  --resolution_flag                       false
% 7.76/1.50  --res_lit_sel                           adaptive
% 7.76/1.50  --res_lit_sel_side                      none
% 7.76/1.50  --res_ordering                          kbo
% 7.76/1.50  --res_to_prop_solver                    active
% 7.76/1.50  --res_prop_simpl_new                    false
% 7.76/1.50  --res_prop_simpl_given                  true
% 7.76/1.50  --res_passive_queue_type                priority_queues
% 7.76/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.50  --res_passive_queues_freq               [15;5]
% 7.76/1.50  --res_forward_subs                      full
% 7.76/1.50  --res_backward_subs                     full
% 7.76/1.50  --res_forward_subs_resolution           true
% 7.76/1.50  --res_backward_subs_resolution          true
% 7.76/1.50  --res_orphan_elimination                true
% 7.76/1.50  --res_time_limit                        2.
% 7.76/1.50  --res_out_proof                         true
% 7.76/1.50  
% 7.76/1.50  ------ Superposition Options
% 7.76/1.50  
% 7.76/1.50  --superposition_flag                    true
% 7.76/1.50  --sup_passive_queue_type                priority_queues
% 7.76/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.76/1.50  --demod_completeness_check              fast
% 7.76/1.50  --demod_use_ground                      true
% 7.76/1.50  --sup_to_prop_solver                    passive
% 7.76/1.50  --sup_prop_simpl_new                    true
% 7.76/1.50  --sup_prop_simpl_given                  true
% 7.76/1.50  --sup_fun_splitting                     true
% 7.76/1.50  --sup_smt_interval                      50000
% 7.76/1.50  
% 7.76/1.50  ------ Superposition Simplification Setup
% 7.76/1.50  
% 7.76/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.76/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.76/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.76/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.76/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.76/1.50  --sup_immed_triv                        [TrivRules]
% 7.76/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_immed_bw_main                     []
% 7.76/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.76/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.50  --sup_input_bw                          []
% 7.76/1.50  
% 7.76/1.50  ------ Combination Options
% 7.76/1.50  
% 7.76/1.50  --comb_res_mult                         3
% 7.76/1.50  --comb_sup_mult                         2
% 7.76/1.50  --comb_inst_mult                        10
% 7.76/1.50  
% 7.76/1.50  ------ Debug Options
% 7.76/1.50  
% 7.76/1.50  --dbg_backtrace                         false
% 7.76/1.50  --dbg_dump_prop_clauses                 false
% 7.76/1.50  --dbg_dump_prop_clauses_file            -
% 7.76/1.50  --dbg_out_stat                          false
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  ------ Proving...
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  % SZS status Theorem for theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  fof(f6,axiom,(
% 7.76/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.76/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f21,plain,(
% 7.76/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.76/1.50    inference(nnf_transformation,[],[f6])).
% 7.76/1.50  
% 7.76/1.50  fof(f31,plain,(
% 7.76/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.76/1.50    inference(cnf_transformation,[],[f21])).
% 7.76/1.50  
% 7.76/1.50  fof(f8,axiom,(
% 7.76/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 7.76/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f18,plain,(
% 7.76/1.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.76/1.50    inference(ennf_transformation,[],[f8])).
% 7.76/1.50  
% 7.76/1.50  fof(f19,plain,(
% 7.76/1.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.76/1.50    inference(flattening,[],[f18])).
% 7.76/1.50  
% 7.76/1.50  fof(f34,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f19])).
% 7.76/1.50  
% 7.76/1.50  fof(f9,conjecture,(
% 7.76/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 7.76/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f10,negated_conjecture,(
% 7.76/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 7.76/1.50    inference(negated_conjecture,[],[f9])).
% 7.76/1.50  
% 7.76/1.50  fof(f20,plain,(
% 7.76/1.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.76/1.50    inference(ennf_transformation,[],[f10])).
% 7.76/1.50  
% 7.76/1.50  fof(f24,plain,(
% 7.76/1.50    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f23,plain,(
% 7.76/1.50    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f22,plain,(
% 7.76/1.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.76/1.50    introduced(choice_axiom,[])).
% 7.76/1.50  
% 7.76/1.50  fof(f25,plain,(
% 7.76/1.50    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.76/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23,f22])).
% 7.76/1.50  
% 7.76/1.50  fof(f35,plain,(
% 7.76/1.50    l1_pre_topc(sK0)),
% 7.76/1.50    inference(cnf_transformation,[],[f25])).
% 7.76/1.50  
% 7.76/1.50  fof(f3,axiom,(
% 7.76/1.50    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.76/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f11,plain,(
% 7.76/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 7.76/1.50    inference(ennf_transformation,[],[f3])).
% 7.76/1.50  
% 7.76/1.50  fof(f12,plain,(
% 7.76/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 7.76/1.50    inference(flattening,[],[f11])).
% 7.76/1.50  
% 7.76/1.50  fof(f28,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f12])).
% 7.76/1.50  
% 7.76/1.50  fof(f7,axiom,(
% 7.76/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.76/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f16,plain,(
% 7.76/1.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.76/1.50    inference(ennf_transformation,[],[f7])).
% 7.76/1.50  
% 7.76/1.50  fof(f17,plain,(
% 7.76/1.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.76/1.50    inference(flattening,[],[f16])).
% 7.76/1.50  
% 7.76/1.50  fof(f33,plain,(
% 7.76/1.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f17])).
% 7.76/1.50  
% 7.76/1.50  fof(f36,plain,(
% 7.76/1.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.76/1.50    inference(cnf_transformation,[],[f25])).
% 7.76/1.50  
% 7.76/1.50  fof(f37,plain,(
% 7.76/1.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.76/1.50    inference(cnf_transformation,[],[f25])).
% 7.76/1.50  
% 7.76/1.50  fof(f4,axiom,(
% 7.76/1.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.76/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f13,plain,(
% 7.76/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.76/1.50    inference(ennf_transformation,[],[f4])).
% 7.76/1.50  
% 7.76/1.50  fof(f14,plain,(
% 7.76/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.76/1.50    inference(flattening,[],[f13])).
% 7.76/1.50  
% 7.76/1.50  fof(f29,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f14])).
% 7.76/1.50  
% 7.76/1.50  fof(f5,axiom,(
% 7.76/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.76/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f15,plain,(
% 7.76/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.76/1.50    inference(ennf_transformation,[],[f5])).
% 7.76/1.50  
% 7.76/1.50  fof(f30,plain,(
% 7.76/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.76/1.50    inference(cnf_transformation,[],[f15])).
% 7.76/1.50  
% 7.76/1.50  fof(f32,plain,(
% 7.76/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f21])).
% 7.76/1.50  
% 7.76/1.50  fof(f38,plain,(
% 7.76/1.50    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 7.76/1.50    inference(cnf_transformation,[],[f25])).
% 7.76/1.50  
% 7.76/1.50  fof(f2,axiom,(
% 7.76/1.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.76/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f27,plain,(
% 7.76/1.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f2])).
% 7.76/1.50  
% 7.76/1.50  fof(f1,axiom,(
% 7.76/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.76/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.50  
% 7.76/1.50  fof(f26,plain,(
% 7.76/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.76/1.50    inference(cnf_transformation,[],[f1])).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.76/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_314,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
% 7.76/1.50      | r1_tarski(X0_39,X1_39) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1709,plain,
% 7.76/1.50      ( ~ m1_subset_1(k3_xboole_0(X0_39,X1_39),k1_zfmisc_1(X2_39))
% 7.76/1.50      | r1_tarski(k3_xboole_0(X0_39,X1_39),X2_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_314]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6147,plain,
% 7.76/1.50      ( ~ m1_subset_1(k3_xboole_0(X0_39,sK2),k1_zfmisc_1(X1_39))
% 7.76/1.50      | r1_tarski(k3_xboole_0(X0_39,sK2),X1_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_1709]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_26760,plain,
% 7.76/1.50      ( ~ m1_subset_1(k3_xboole_0(X0_39,sK2),k1_zfmisc_1(sK2))
% 7.76/1.50      | r1_tarski(k3_xboole_0(X0_39,sK2),sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_6147]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_26764,plain,
% 7.76/1.50      ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))
% 7.76/1.50      | r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_26760]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_8,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.76/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.76/1.50      | ~ r1_tarski(X0,X2)
% 7.76/1.50      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 7.76/1.50      | ~ l1_pre_topc(X1) ),
% 7.76/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_12,negated_conjecture,
% 7.76/1.50      ( l1_pre_topc(sK0) ),
% 7.76/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_166,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.76/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.76/1.50      | ~ r1_tarski(X0,X2)
% 7.76/1.50      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 7.76/1.50      | sK0 != X1 ),
% 7.76/1.50      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_167,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ r1_tarski(X1,X0)
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
% 7.76/1.50      inference(unflattening,[status(thm)],[c_166]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_309,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ r1_tarski(X1_39,X0_39)
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,X1_39),k2_pre_topc(sK0,X0_39)) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_167]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1124,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ m1_subset_1(k3_xboole_0(X1_39,X2_39),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X1_39,X2_39)),k2_pre_topc(sK0,X0_39))
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(X1_39,X2_39),X0_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_309]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_16871,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,X0_39))
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(sK1,sK2),X0_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_1124]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_26007,plain,
% 7.76/1.50      ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_16871]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2,plain,
% 7.76/1.50      ( ~ r1_tarski(X0,X1)
% 7.76/1.50      | ~ r1_tarski(X0,X2)
% 7.76/1.50      | r1_tarski(X0,k3_xboole_0(X2,X1)) ),
% 7.76/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_317,plain,
% 7.76/1.50      ( ~ r1_tarski(X0_39,X1_39)
% 7.76/1.50      | ~ r1_tarski(X0_39,X2_39)
% 7.76/1.50      | r1_tarski(X0_39,k3_xboole_0(X2_39,X1_39)) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_618,plain,
% 7.76/1.50      ( r1_tarski(X0_39,X1_39) != iProver_top
% 7.76/1.50      | r1_tarski(X0_39,X2_39) != iProver_top
% 7.76/1.50      | r1_tarski(X0_39,k3_xboole_0(X1_39,X2_39)) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_7,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.76/1.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.76/1.50      | ~ l1_pre_topc(X1) ),
% 7.76/1.50      inference(cnf_transformation,[],[f33]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_184,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.76/1.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.76/1.50      | sK0 != X1 ),
% 7.76/1.50      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_185,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.76/1.50      inference(unflattening,[status(thm)],[c_184]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_308,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_185]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_627,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_621,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39)) != iProver_top
% 7.76/1.50      | r1_tarski(X0_39,X1_39) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1108,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,X0_39),u1_struct_0(sK0)) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_627,c_621]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_11,negated_conjecture,
% 7.76/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.76/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_311,negated_conjecture,
% 7.76/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_624,plain,
% 7.76/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_10,negated_conjecture,
% 7.76/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.76/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_312,negated_conjecture,
% 7.76/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_623,plain,
% 7.76/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_626,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | r1_tarski(X1_39,X0_39) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,X1_39),k2_pre_topc(sK0,X0_39)) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_3,plain,
% 7.76/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.76/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_316,plain,
% 7.76/1.50      ( ~ r1_tarski(X0_39,X1_39)
% 7.76/1.50      | ~ r1_tarski(X1_39,X2_39)
% 7.76/1.50      | r1_tarski(X0_39,X2_39) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_619,plain,
% 7.76/1.50      ( r1_tarski(X0_39,X1_39) != iProver_top
% 7.76/1.50      | r1_tarski(X1_39,X2_39) != iProver_top
% 7.76/1.50      | r1_tarski(X0_39,X2_39) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1116,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | m1_subset_1(X1_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | r1_tarski(X1_39,X0_39) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,X0_39),X2_39) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,X1_39),X2_39) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_626,c_619]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1410,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | r1_tarski(X0_39,sK2) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,X0_39),X1_39) = iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,sK2),X1_39) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_623,c_1116]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1533,plain,
% 7.76/1.50      ( r1_tarski(k2_pre_topc(sK0,sK2),X0_39) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,sK1),X0_39) = iProver_top
% 7.76/1.50      | r1_tarski(sK1,sK2) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_624,c_1410]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1547,plain,
% 7.76/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 7.76/1.50      | r1_tarski(sK1,sK2) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_1108,c_1533]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_14,plain,
% 7.76/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_360,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_362,plain,
% 7.76/1.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.76/1.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_360]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_723,plain,
% 7.76/1.50      ( ~ m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,X0_39),u1_struct_0(sK0)) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_314]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_724,plain,
% 7.76/1.50      ( m1_subset_1(k2_pre_topc(sK0,X0_39),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,X0_39),u1_struct_0(sK0)) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_726,plain,
% 7.76/1.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_724]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2150,plain,
% 7.76/1.50      ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 7.76/1.50      inference(global_propositional_subsumption,
% 7.76/1.50                [status(thm)],
% 7.76/1.50                [c_1547,c_14,c_362,c_726]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1411,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | r1_tarski(X0_39,sK1) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,X0_39),X1_39) = iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,sK1),X1_39) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_624,c_1116]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1633,plain,
% 7.76/1.50      ( r1_tarski(k2_pre_topc(sK0,sK2),X0_39) = iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,sK1),X0_39) != iProver_top
% 7.76/1.50      | r1_tarski(sK2,sK1) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_623,c_1411]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2156,plain,
% 7.76/1.50      ( r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) = iProver_top
% 7.76/1.50      | r1_tarski(sK2,sK1) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_2150,c_1633]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_15,plain,
% 7.76/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1528,plain,
% 7.76/1.50      ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_723]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1529,plain,
% 7.76/1.50      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_1528]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2031,plain,
% 7.76/1.50      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_308]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2032,plain,
% 7.76/1.50      ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.76/1.50      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_2031]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2163,plain,
% 7.76/1.50      ( r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
% 7.76/1.50      inference(global_propositional_subsumption,
% 7.76/1.50                [status(thm)],
% 7.76/1.50                [c_2156,c_15,c_1529,c_2032]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_4,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.76/1.50      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.76/1.50      inference(cnf_transformation,[],[f30]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5,plain,
% 7.76/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.76/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_93,plain,
% 7.76/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.76/1.50      inference(prop_impl,[status(thm)],[c_5]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_94,plain,
% 7.76/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.76/1.50      inference(renaming,[status(thm)],[c_93]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_115,plain,
% 7.76/1.50      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.76/1.50      inference(bin_hyper_res,[status(thm)],[c_4,c_94]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_310,plain,
% 7.76/1.50      ( ~ r1_tarski(X0_39,X1_39)
% 7.76/1.50      | k9_subset_1(X1_39,X2_39,X0_39) = k3_xboole_0(X2_39,X0_39) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_115]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_625,plain,
% 7.76/1.50      ( k9_subset_1(X0_39,X1_39,X2_39) = k3_xboole_0(X1_39,X2_39)
% 7.76/1.50      | r1_tarski(X2_39,X0_39) != iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2168,plain,
% 7.76/1.50      ( k9_subset_1(u1_struct_0(sK0),X0_39,k2_pre_topc(sK0,sK2)) = k3_xboole_0(X0_39,k2_pre_topc(sK0,sK2)) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_2163,c_625]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1106,plain,
% 7.76/1.50      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_623,c_621]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1645,plain,
% 7.76/1.50      ( k9_subset_1(u1_struct_0(sK0),X0_39,sK2) = k3_xboole_0(X0_39,sK2) ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_1106,c_625]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_9,negated_conjecture,
% 7.76/1.50      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
% 7.76/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_313,negated_conjecture,
% 7.76/1.50      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_622,plain,
% 7.76/1.50      ( r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 7.76/1.50      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1995,plain,
% 7.76/1.50      ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 7.76/1.50      inference(demodulation,[status(thm)],[c_1645,c_622]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_24797,plain,
% 7.76/1.50      ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) != iProver_top ),
% 7.76/1.50      inference(demodulation,[status(thm)],[c_2168,c_1995]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25185,plain,
% 7.76/1.50      ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2)) != iProver_top
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 7.76/1.50      inference(superposition,[status(thm)],[c_618,c_24797]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_25186,plain,
% 7.76/1.50      ( ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))
% 7.76/1.50      | ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1)) ),
% 7.76/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_25185]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_322,plain,( X0_40 = X0_40 ),theory(equality) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_19047,plain,
% 7.76/1.50      ( k1_zfmisc_1(sK2) = k1_zfmisc_1(sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_322]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_323,plain,
% 7.76/1.50      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 7.76/1.50      theory(equality) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1060,plain,
% 7.76/1.50      ( X0_39 != X1_39
% 7.76/1.50      | X0_39 = k3_xboole_0(X2_39,X3_39)
% 7.76/1.50      | k3_xboole_0(X2_39,X3_39) != X1_39 ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_323]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1847,plain,
% 7.76/1.50      ( X0_39 != k3_xboole_0(X1_39,X2_39)
% 7.76/1.50      | X0_39 = k3_xboole_0(X2_39,X1_39)
% 7.76/1.50      | k3_xboole_0(X2_39,X1_39) != k3_xboole_0(X1_39,X2_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_1060]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_3813,plain,
% 7.76/1.50      ( k3_xboole_0(X0_39,X1_39) != k3_xboole_0(X1_39,X0_39)
% 7.76/1.50      | k3_xboole_0(X1_39,X0_39) != k3_xboole_0(X1_39,X0_39)
% 7.76/1.50      | k3_xboole_0(X1_39,X0_39) = k3_xboole_0(X0_39,X1_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_1847]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_15625,plain,
% 7.76/1.50      ( k3_xboole_0(sK2,sK1) != k3_xboole_0(sK1,sK2)
% 7.76/1.50      | k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1)
% 7.76/1.50      | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_3813]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_666,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ m1_subset_1(k3_xboole_0(X0_39,X1_39),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(X0_39,X1_39)),k2_pre_topc(sK0,X0_39))
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_309]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_14918,plain,
% 7.76/1.50      ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK1))
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_666]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_315,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
% 7.76/1.50      | ~ r1_tarski(X0_39,X1_39) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_884,plain,
% 7.76/1.50      ( m1_subset_1(k3_xboole_0(X0_39,X1_39),k1_zfmisc_1(X0_39))
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_315]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_12825,plain,
% 7.76/1.50      ( m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(sK2))
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(sK2,sK1),sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_884]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_740,plain,
% 7.76/1.50      ( ~ r1_tarski(X0_39,X1_39)
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(X0_39,X2_39),X0_39)
% 7.76/1.50      | r1_tarski(k3_xboole_0(X0_39,X2_39),X1_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_316]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1146,plain,
% 7.76/1.50      ( ~ r1_tarski(X0_39,u1_struct_0(sK0))
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39)
% 7.76/1.50      | r1_tarski(k3_xboole_0(X0_39,X1_39),u1_struct_0(sK0)) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_740]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_12813,plain,
% 7.76/1.50      ( r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0))
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
% 7.76/1.50      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_1146]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_327,plain,
% 7.76/1.50      ( ~ m1_subset_1(X0_39,X0_40)
% 7.76/1.50      | m1_subset_1(X1_39,X1_40)
% 7.76/1.50      | X1_40 != X0_40
% 7.76/1.50      | X1_39 != X0_39 ),
% 7.76/1.50      theory(equality) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1088,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,X0_40)
% 7.76/1.50      | ~ m1_subset_1(k3_xboole_0(X1_39,X2_39),k1_zfmisc_1(X1_39))
% 7.76/1.50      | X0_40 != k1_zfmisc_1(X1_39)
% 7.76/1.50      | X0_39 != k3_xboole_0(X1_39,X2_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_327]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1759,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(X1_39))
% 7.76/1.50      | ~ m1_subset_1(k3_xboole_0(X1_39,X2_39),k1_zfmisc_1(X1_39))
% 7.76/1.50      | k1_zfmisc_1(X1_39) != k1_zfmisc_1(X1_39)
% 7.76/1.50      | X0_39 != k3_xboole_0(X1_39,X2_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_1088]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1938,plain,
% 7.76/1.50      ( ~ m1_subset_1(k3_xboole_0(X0_39,X1_39),k1_zfmisc_1(X0_39))
% 7.76/1.50      | m1_subset_1(k3_xboole_0(X1_39,X0_39),k1_zfmisc_1(X0_39))
% 7.76/1.50      | k1_zfmisc_1(X0_39) != k1_zfmisc_1(X0_39)
% 7.76/1.50      | k3_xboole_0(X1_39,X0_39) != k3_xboole_0(X0_39,X1_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_1759]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6359,plain,
% 7.76/1.50      ( m1_subset_1(k3_xboole_0(X0_39,sK2),k1_zfmisc_1(sK2))
% 7.76/1.50      | ~ m1_subset_1(k3_xboole_0(sK2,X0_39),k1_zfmisc_1(sK2))
% 7.76/1.50      | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2)
% 7.76/1.50      | k3_xboole_0(X0_39,sK2) != k3_xboole_0(sK2,X0_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_1938]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6365,plain,
% 7.76/1.50      ( ~ m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(sK2))
% 7.76/1.50      | m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(sK2))
% 7.76/1.50      | k1_zfmisc_1(sK2) != k1_zfmisc_1(sK2)
% 7.76/1.50      | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_6359]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1,plain,
% 7.76/1.50      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 7.76/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_318,plain,
% 7.76/1.50      ( r1_tarski(k3_xboole_0(X0_39,X1_39),X0_39) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6211,plain,
% 7.76/1.50      ( r1_tarski(k3_xboole_0(X0_39,sK2),X0_39) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_318]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_6213,plain,
% 7.76/1.50      ( r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_6211]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_0,plain,
% 7.76/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.76/1.50      inference(cnf_transformation,[],[f26]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_319,plain,
% 7.76/1.50      ( k3_xboole_0(X0_39,X1_39) = k3_xboole_0(X1_39,X0_39) ),
% 7.76/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5821,plain,
% 7.76/1.50      ( k3_xboole_0(sK2,X0_39) = k3_xboole_0(X0_39,sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_319]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5822,plain,
% 7.76/1.50      ( k3_xboole_0(sK2,sK1) = k3_xboole_0(sK1,sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_5821]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_321,plain,( X0_39 = X0_39 ),theory(equality) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5816,plain,
% 7.76/1.50      ( k3_xboole_0(X0_39,sK2) = k3_xboole_0(X0_39,sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_321]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5817,plain,
% 7.76/1.50      ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_5816]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_1329,plain,
% 7.76/1.50      ( m1_subset_1(X0_39,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ r1_tarski(X0_39,u1_struct_0(sK0)) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_315]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_5110,plain,
% 7.76/1.50      ( m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | ~ r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_1329]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2238,plain,
% 7.76/1.50      ( r1_tarski(k3_xboole_0(sK2,X0_39),sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_318]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_2240,plain,
% 7.76/1.50      ( r1_tarski(k3_xboole_0(sK2,sK1),sK2) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_2238]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(c_720,plain,
% 7.76/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.76/1.50      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.76/1.50      inference(instantiation,[status(thm)],[c_314]) ).
% 7.76/1.50  
% 7.76/1.50  cnf(contradiction,plain,
% 7.76/1.50      ( $false ),
% 7.76/1.50      inference(minisat,
% 7.76/1.50                [status(thm)],
% 7.76/1.50                [c_26764,c_26007,c_25186,c_19047,c_15625,c_14918,c_12825,
% 7.76/1.50                 c_12813,c_6365,c_6213,c_5822,c_5817,c_5110,c_2240,c_720,
% 7.76/1.50                 c_10,c_11]) ).
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.76/1.50  
% 7.76/1.50  ------                               Statistics
% 7.76/1.50  
% 7.76/1.50  ------ General
% 7.76/1.50  
% 7.76/1.50  abstr_ref_over_cycles:                  0
% 7.76/1.50  abstr_ref_under_cycles:                 0
% 7.76/1.50  gc_basic_clause_elim:                   0
% 7.76/1.50  forced_gc_time:                         0
% 7.76/1.50  parsing_time:                           0.008
% 7.76/1.50  unif_index_cands_time:                  0.
% 7.76/1.50  unif_index_add_time:                    0.
% 7.76/1.50  orderings_time:                         0.
% 7.76/1.50  out_proof_time:                         0.011
% 7.76/1.50  total_time:                             0.785
% 7.76/1.50  num_of_symbols:                         45
% 7.76/1.50  num_of_terms:                           27246
% 7.76/1.50  
% 7.76/1.50  ------ Preprocessing
% 7.76/1.50  
% 7.76/1.50  num_of_splits:                          0
% 7.76/1.50  num_of_split_atoms:                     0
% 7.76/1.50  num_of_reused_defs:                     0
% 7.76/1.50  num_eq_ax_congr_red:                    8
% 7.76/1.50  num_of_sem_filtered_clauses:            1
% 7.76/1.50  num_of_subtypes:                        3
% 7.76/1.50  monotx_restored_types:                  0
% 7.76/1.50  sat_num_of_epr_types:                   0
% 7.76/1.50  sat_num_of_non_cyclic_types:            0
% 7.76/1.50  sat_guarded_non_collapsed_types:        0
% 7.76/1.50  num_pure_diseq_elim:                    0
% 7.76/1.50  simp_replaced_by:                       0
% 7.76/1.50  res_preprocessed:                       66
% 7.76/1.50  prep_upred:                             0
% 7.76/1.50  prep_unflattend:                        2
% 7.76/1.50  smt_new_axioms:                         0
% 7.76/1.50  pred_elim_cands:                        2
% 7.76/1.50  pred_elim:                              1
% 7.76/1.50  pred_elim_cl:                           1
% 7.76/1.50  pred_elim_cycles:                       3
% 7.76/1.50  merged_defs:                            8
% 7.76/1.50  merged_defs_ncl:                        0
% 7.76/1.50  bin_hyper_res:                          9
% 7.76/1.50  prep_cycles:                            4
% 7.76/1.50  pred_elim_time:                         0.001
% 7.76/1.50  splitting_time:                         0.
% 7.76/1.50  sem_filter_time:                        0.
% 7.76/1.50  monotx_time:                            0.
% 7.76/1.50  subtype_inf_time:                       0.
% 7.76/1.50  
% 7.76/1.50  ------ Problem properties
% 7.76/1.50  
% 7.76/1.50  clauses:                                12
% 7.76/1.50  conjectures:                            3
% 7.76/1.50  epr:                                    1
% 7.76/1.50  horn:                                   12
% 7.76/1.50  ground:                                 3
% 7.76/1.50  unary:                                  5
% 7.76/1.50  binary:                                 4
% 7.76/1.50  lits:                                   23
% 7.76/1.50  lits_eq:                                2
% 7.76/1.50  fd_pure:                                0
% 7.76/1.50  fd_pseudo:                              0
% 7.76/1.50  fd_cond:                                0
% 7.76/1.50  fd_pseudo_cond:                         0
% 7.76/1.50  ac_symbols:                             0
% 7.76/1.50  
% 7.76/1.50  ------ Propositional Solver
% 7.76/1.50  
% 7.76/1.50  prop_solver_calls:                      33
% 7.76/1.50  prop_fast_solver_calls:                 663
% 7.76/1.50  smt_solver_calls:                       0
% 7.76/1.50  smt_fast_solver_calls:                  0
% 7.76/1.50  prop_num_of_clauses:                    10446
% 7.76/1.50  prop_preprocess_simplified:             17948
% 7.76/1.50  prop_fo_subsumed:                       10
% 7.76/1.50  prop_solver_time:                       0.
% 7.76/1.50  smt_solver_time:                        0.
% 7.76/1.50  smt_fast_solver_time:                   0.
% 7.76/1.50  prop_fast_solver_time:                  0.
% 7.76/1.50  prop_unsat_core_time:                   0.001
% 7.76/1.50  
% 7.76/1.50  ------ QBF
% 7.76/1.50  
% 7.76/1.50  qbf_q_res:                              0
% 7.76/1.50  qbf_num_tautologies:                    0
% 7.76/1.50  qbf_prep_cycles:                        0
% 7.76/1.50  
% 7.76/1.50  ------ BMC1
% 7.76/1.50  
% 7.76/1.50  bmc1_current_bound:                     -1
% 7.76/1.50  bmc1_last_solved_bound:                 -1
% 7.76/1.50  bmc1_unsat_core_size:                   -1
% 7.76/1.50  bmc1_unsat_core_parents_size:           -1
% 7.76/1.50  bmc1_merge_next_fun:                    0
% 7.76/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.76/1.50  
% 7.76/1.50  ------ Instantiation
% 7.76/1.50  
% 7.76/1.50  inst_num_of_clauses:                    2271
% 7.76/1.50  inst_num_in_passive:                    1281
% 7.76/1.50  inst_num_in_active:                     748
% 7.76/1.50  inst_num_in_unprocessed:                242
% 7.76/1.50  inst_num_of_loops:                      816
% 7.76/1.50  inst_num_of_learning_restarts:          0
% 7.76/1.50  inst_num_moves_active_passive:          63
% 7.76/1.50  inst_lit_activity:                      0
% 7.76/1.50  inst_lit_activity_moves:                0
% 7.76/1.50  inst_num_tautologies:                   0
% 7.76/1.50  inst_num_prop_implied:                  0
% 7.76/1.50  inst_num_existing_simplified:           0
% 7.76/1.50  inst_num_eq_res_simplified:             0
% 7.76/1.50  inst_num_child_elim:                    0
% 7.76/1.50  inst_num_of_dismatching_blockings:      1824
% 7.76/1.50  inst_num_of_non_proper_insts:           2956
% 7.76/1.50  inst_num_of_duplicates:                 0
% 7.76/1.50  inst_inst_num_from_inst_to_res:         0
% 7.76/1.50  inst_dismatching_checking_time:         0.
% 7.76/1.50  
% 7.76/1.50  ------ Resolution
% 7.76/1.50  
% 7.76/1.50  res_num_of_clauses:                     0
% 7.76/1.50  res_num_in_passive:                     0
% 7.76/1.50  res_num_in_active:                      0
% 7.76/1.50  res_num_of_loops:                       70
% 7.76/1.50  res_forward_subset_subsumed:            190
% 7.76/1.50  res_backward_subset_subsumed:           6
% 7.76/1.50  res_forward_subsumed:                   0
% 7.76/1.50  res_backward_subsumed:                  0
% 7.76/1.50  res_forward_subsumption_resolution:     0
% 7.76/1.50  res_backward_subsumption_resolution:    0
% 7.76/1.50  res_clause_to_clause_subsumption:       35160
% 7.76/1.50  res_orphan_elimination:                 0
% 7.76/1.50  res_tautology_del:                      216
% 7.76/1.50  res_num_eq_res_simplified:              0
% 7.76/1.50  res_num_sel_changes:                    0
% 7.76/1.50  res_moves_from_active_to_pass:          0
% 7.76/1.50  
% 7.76/1.50  ------ Superposition
% 7.76/1.50  
% 7.76/1.50  sup_time_total:                         0.
% 7.76/1.50  sup_time_generating:                    0.
% 7.76/1.50  sup_time_sim_full:                      0.
% 7.76/1.50  sup_time_sim_immed:                     0.
% 7.76/1.50  
% 7.76/1.50  sup_num_of_clauses:                     1460
% 7.76/1.50  sup_num_in_active:                      160
% 7.76/1.50  sup_num_in_passive:                     1300
% 7.76/1.50  sup_num_of_loops:                       162
% 7.76/1.50  sup_fw_superposition:                   5339
% 7.76/1.50  sup_bw_superposition:                   3363
% 7.76/1.50  sup_immediate_simplified:               144
% 7.76/1.50  sup_given_eliminated:                   0
% 7.76/1.50  comparisons_done:                       0
% 7.76/1.50  comparisons_avoided:                    0
% 7.76/1.50  
% 7.76/1.50  ------ Simplifications
% 7.76/1.50  
% 7.76/1.50  
% 7.76/1.50  sim_fw_subset_subsumed:                 26
% 7.76/1.50  sim_bw_subset_subsumed:                 5
% 7.76/1.50  sim_fw_subsumed:                        108
% 7.76/1.50  sim_bw_subsumed:                        14
% 7.76/1.50  sim_fw_subsumption_res:                 0
% 7.76/1.50  sim_bw_subsumption_res:                 0
% 7.76/1.50  sim_tautology_del:                      7
% 7.76/1.50  sim_eq_tautology_del:                   0
% 7.76/1.50  sim_eq_res_simp:                        0
% 7.76/1.50  sim_fw_demodulated:                     0
% 7.76/1.50  sim_bw_demodulated:                     2
% 7.76/1.50  sim_light_normalised:                   0
% 7.76/1.50  sim_joinable_taut:                      0
% 7.76/1.50  sim_joinable_simp:                      0
% 7.76/1.50  sim_ac_normalised:                      0
% 7.76/1.50  sim_smt_subsumption:                    0
% 7.76/1.50  
%------------------------------------------------------------------------------
