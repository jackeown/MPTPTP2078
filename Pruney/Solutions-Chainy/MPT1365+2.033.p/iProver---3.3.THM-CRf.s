%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:03 EST 2020

% Result     : Theorem 1.17s
% Output     : CNFRefutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 274 expanded)
%              Number of clauses        :   66 (  83 expanded)
%              Number of leaves         :   12 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  431 (1826 expanded)
%              Number of equality atoms :   72 (  74 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v2_compts_1(X2,X0)
          & v2_compts_1(X1,X0)
          & v8_pre_topc(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v2_compts_1(sK2,X0)
        & v2_compts_1(X1,X0)
        & v8_pre_topc(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v2_compts_1(X2,X0)
            & v2_compts_1(sK1,X0)
            & v8_pre_topc(X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24,f23])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v4_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_360,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_646,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_5,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k3_xboole_0(X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_225,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k3_xboole_0(X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_226,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k3_xboole_0(X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k3_xboole_0(X1,X0),sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ v4_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_226,c_15])).

cnf(c_231,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k3_xboole_0(X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_230])).

cnf(c_356,plain,
    ( ~ v4_pre_topc(X0_43,sK0)
    | ~ v4_pre_topc(X1_43,sK0)
    | v4_pre_topc(k3_xboole_0(X1_43,X0_43),sK0)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_231])).

cnf(c_650,plain,
    ( v4_pre_topc(X0_43,sK0) != iProver_top
    | v4_pre_topc(X1_43,sK0) != iProver_top
    | v4_pre_topc(k3_xboole_0(X1_43,X0_43),sK0) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_1807,plain,
    ( v4_pre_topc(X0_43,sK0) != iProver_top
    | v4_pre_topc(k3_xboole_0(X0_43,sK2),sK0) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_646,c_650])).

cnf(c_1837,plain,
    ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) = iProver_top
    | v4_pre_topc(sK2,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1807])).

cnf(c_376,plain,
    ( ~ v4_pre_topc(X0_43,X0_44)
    | v4_pre_topc(X1_43,X0_44)
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_910,plain,
    ( ~ v4_pre_topc(X0_43,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_43 ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_1372,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_910])).

cnf(c_1373,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
    | v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1372])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_366,plain,
    ( r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(k3_subset_1(X0_46,X1_43),k3_subset_1(X0_46,X0_43))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_46))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_804,plain,
    ( r1_tarski(X0_43,sK1)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),X0_43))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_965,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_967,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) = iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_965])).

cnf(c_6,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_174,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_175,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_179,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_175,c_15,c_14])).

cnf(c_358,plain,
    ( ~ v2_compts_1(X0_43,sK0)
    | v4_pre_topc(X0_43,sK0)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_179])).

cnf(c_648,plain,
    ( v2_compts_1(X0_43,sK0) != iProver_top
    | v4_pre_topc(X0_43,sK0) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_921,plain,
    ( v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_646,c_648])).

cnf(c_4,plain,
    ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_364,plain,
    ( r1_tarski(k3_subset_1(X0_46,X0_43),k3_subset_1(X0_46,k9_subset_1(X0_46,X0_43,X1_43)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_46))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_789,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_43),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_43,sK2)))
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_790,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_43),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_43,sK2))) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_792,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_46))
    | k9_subset_1(X0_46,X1_43,X0_43) = k3_xboole_0(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_779,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),X0_43,sK2) = k3_xboole_0(X0_43,sK2) ),
    inference(instantiation,[status(thm)],[c_367])).

cnf(c_781,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_779])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_46))
    | m1_subset_1(k9_subset_1(X0_46,X1_43,X0_43),k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_754,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_43,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_755,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_43,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_757,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_7,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_199,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_200,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | ~ v4_pre_topc(X1,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v2_compts_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_200,c_15])).

cnf(c_203,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_357,plain,
    ( ~ v2_compts_1(X0_43,sK0)
    | v2_compts_1(X1_43,sK0)
    | ~ v4_pre_topc(X1_43,sK0)
    | ~ r1_tarski(X1_43,X0_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_749,plain,
    ( ~ v2_compts_1(X0_43,sK0)
    | v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_750,plain,
    ( v2_compts_1(X0_43,sK0) != iProver_top
    | v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0_43) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_752,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
    | v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top
    | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_406,plain,
    ( v2_compts_1(X0_43,sK0) != iProver_top
    | v4_pre_topc(X0_43,sK0) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_408,plain,
    ( v2_compts_1(sK1,sK0) != iProver_top
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_8,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_23,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_22,plain,
    ( v2_compts_1(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,plain,
    ( v2_compts_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1837,c_1373,c_967,c_921,c_792,c_781,c_757,c_752,c_408,c_23,c_22,c_21,c_19,c_12,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.17/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.17/1.05  
% 1.17/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.17/1.05  
% 1.17/1.05  ------  iProver source info
% 1.17/1.05  
% 1.17/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.17/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.17/1.05  git: non_committed_changes: false
% 1.17/1.05  git: last_make_outside_of_git: false
% 1.17/1.05  
% 1.17/1.05  ------ 
% 1.17/1.05  
% 1.17/1.05  ------ Input Options
% 1.17/1.05  
% 1.17/1.05  --out_options                           all
% 1.17/1.05  --tptp_safe_out                         true
% 1.17/1.05  --problem_path                          ""
% 1.17/1.05  --include_path                          ""
% 1.17/1.05  --clausifier                            res/vclausify_rel
% 1.17/1.05  --clausifier_options                    --mode clausify
% 1.17/1.05  --stdin                                 false
% 1.17/1.05  --stats_out                             all
% 1.17/1.05  
% 1.17/1.05  ------ General Options
% 1.17/1.05  
% 1.17/1.05  --fof                                   false
% 1.17/1.05  --time_out_real                         305.
% 1.17/1.05  --time_out_virtual                      -1.
% 1.17/1.05  --symbol_type_check                     false
% 1.17/1.05  --clausify_out                          false
% 1.17/1.05  --sig_cnt_out                           false
% 1.17/1.05  --trig_cnt_out                          false
% 1.17/1.05  --trig_cnt_out_tolerance                1.
% 1.17/1.05  --trig_cnt_out_sk_spl                   false
% 1.17/1.05  --abstr_cl_out                          false
% 1.17/1.05  
% 1.17/1.05  ------ Global Options
% 1.17/1.05  
% 1.17/1.05  --schedule                              default
% 1.17/1.05  --add_important_lit                     false
% 1.17/1.05  --prop_solver_per_cl                    1000
% 1.17/1.05  --min_unsat_core                        false
% 1.17/1.05  --soft_assumptions                      false
% 1.17/1.05  --soft_lemma_size                       3
% 1.17/1.05  --prop_impl_unit_size                   0
% 1.17/1.05  --prop_impl_unit                        []
% 1.17/1.05  --share_sel_clauses                     true
% 1.17/1.05  --reset_solvers                         false
% 1.17/1.05  --bc_imp_inh                            [conj_cone]
% 1.17/1.05  --conj_cone_tolerance                   3.
% 1.17/1.05  --extra_neg_conj                        none
% 1.17/1.05  --large_theory_mode                     true
% 1.17/1.05  --prolific_symb_bound                   200
% 1.17/1.05  --lt_threshold                          2000
% 1.17/1.05  --clause_weak_htbl                      true
% 1.17/1.05  --gc_record_bc_elim                     false
% 1.17/1.05  
% 1.17/1.05  ------ Preprocessing Options
% 1.17/1.05  
% 1.17/1.05  --preprocessing_flag                    true
% 1.17/1.05  --time_out_prep_mult                    0.1
% 1.17/1.05  --splitting_mode                        input
% 1.17/1.05  --splitting_grd                         true
% 1.17/1.05  --splitting_cvd                         false
% 1.17/1.05  --splitting_cvd_svl                     false
% 1.17/1.05  --splitting_nvd                         32
% 1.17/1.05  --sub_typing                            true
% 1.17/1.05  --prep_gs_sim                           true
% 1.17/1.05  --prep_unflatten                        true
% 1.17/1.05  --prep_res_sim                          true
% 1.17/1.05  --prep_upred                            true
% 1.17/1.05  --prep_sem_filter                       exhaustive
% 1.17/1.05  --prep_sem_filter_out                   false
% 1.17/1.05  --pred_elim                             true
% 1.17/1.05  --res_sim_input                         true
% 1.17/1.05  --eq_ax_congr_red                       true
% 1.17/1.05  --pure_diseq_elim                       true
% 1.17/1.05  --brand_transform                       false
% 1.17/1.05  --non_eq_to_eq                          false
% 1.17/1.05  --prep_def_merge                        true
% 1.17/1.05  --prep_def_merge_prop_impl              false
% 1.17/1.05  --prep_def_merge_mbd                    true
% 1.17/1.05  --prep_def_merge_tr_red                 false
% 1.17/1.05  --prep_def_merge_tr_cl                  false
% 1.17/1.05  --smt_preprocessing                     true
% 1.17/1.05  --smt_ac_axioms                         fast
% 1.17/1.05  --preprocessed_out                      false
% 1.17/1.05  --preprocessed_stats                    false
% 1.17/1.05  
% 1.17/1.05  ------ Abstraction refinement Options
% 1.17/1.05  
% 1.17/1.05  --abstr_ref                             []
% 1.17/1.05  --abstr_ref_prep                        false
% 1.17/1.05  --abstr_ref_until_sat                   false
% 1.17/1.05  --abstr_ref_sig_restrict                funpre
% 1.17/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/1.05  --abstr_ref_under                       []
% 1.17/1.05  
% 1.17/1.05  ------ SAT Options
% 1.17/1.05  
% 1.17/1.05  --sat_mode                              false
% 1.17/1.05  --sat_fm_restart_options                ""
% 1.17/1.05  --sat_gr_def                            false
% 1.17/1.05  --sat_epr_types                         true
% 1.17/1.05  --sat_non_cyclic_types                  false
% 1.17/1.05  --sat_finite_models                     false
% 1.17/1.05  --sat_fm_lemmas                         false
% 1.17/1.05  --sat_fm_prep                           false
% 1.17/1.05  --sat_fm_uc_incr                        true
% 1.17/1.05  --sat_out_model                         small
% 1.17/1.05  --sat_out_clauses                       false
% 1.17/1.05  
% 1.17/1.05  ------ QBF Options
% 1.17/1.05  
% 1.17/1.05  --qbf_mode                              false
% 1.17/1.05  --qbf_elim_univ                         false
% 1.17/1.05  --qbf_dom_inst                          none
% 1.17/1.05  --qbf_dom_pre_inst                      false
% 1.17/1.05  --qbf_sk_in                             false
% 1.17/1.05  --qbf_pred_elim                         true
% 1.17/1.05  --qbf_split                             512
% 1.17/1.05  
% 1.17/1.05  ------ BMC1 Options
% 1.17/1.05  
% 1.17/1.05  --bmc1_incremental                      false
% 1.17/1.05  --bmc1_axioms                           reachable_all
% 1.17/1.05  --bmc1_min_bound                        0
% 1.17/1.05  --bmc1_max_bound                        -1
% 1.17/1.05  --bmc1_max_bound_default                -1
% 1.17/1.05  --bmc1_symbol_reachability              true
% 1.17/1.05  --bmc1_property_lemmas                  false
% 1.17/1.05  --bmc1_k_induction                      false
% 1.17/1.05  --bmc1_non_equiv_states                 false
% 1.17/1.05  --bmc1_deadlock                         false
% 1.17/1.05  --bmc1_ucm                              false
% 1.17/1.05  --bmc1_add_unsat_core                   none
% 1.17/1.05  --bmc1_unsat_core_children              false
% 1.17/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/1.05  --bmc1_out_stat                         full
% 1.17/1.05  --bmc1_ground_init                      false
% 1.17/1.05  --bmc1_pre_inst_next_state              false
% 1.17/1.05  --bmc1_pre_inst_state                   false
% 1.17/1.05  --bmc1_pre_inst_reach_state             false
% 1.17/1.05  --bmc1_out_unsat_core                   false
% 1.17/1.05  --bmc1_aig_witness_out                  false
% 1.17/1.05  --bmc1_verbose                          false
% 1.17/1.05  --bmc1_dump_clauses_tptp                false
% 1.17/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.17/1.05  --bmc1_dump_file                        -
% 1.17/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.17/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.17/1.05  --bmc1_ucm_extend_mode                  1
% 1.17/1.05  --bmc1_ucm_init_mode                    2
% 1.17/1.05  --bmc1_ucm_cone_mode                    none
% 1.17/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.17/1.05  --bmc1_ucm_relax_model                  4
% 1.17/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.17/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/1.05  --bmc1_ucm_layered_model                none
% 1.17/1.05  --bmc1_ucm_max_lemma_size               10
% 1.17/1.05  
% 1.17/1.05  ------ AIG Options
% 1.17/1.05  
% 1.17/1.05  --aig_mode                              false
% 1.17/1.05  
% 1.17/1.05  ------ Instantiation Options
% 1.17/1.05  
% 1.17/1.05  --instantiation_flag                    true
% 1.17/1.05  --inst_sos_flag                         false
% 1.17/1.05  --inst_sos_phase                        true
% 1.17/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/1.05  --inst_lit_sel_side                     num_symb
% 1.17/1.05  --inst_solver_per_active                1400
% 1.17/1.05  --inst_solver_calls_frac                1.
% 1.17/1.05  --inst_passive_queue_type               priority_queues
% 1.17/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/1.05  --inst_passive_queues_freq              [25;2]
% 1.17/1.05  --inst_dismatching                      true
% 1.17/1.05  --inst_eager_unprocessed_to_passive     true
% 1.17/1.05  --inst_prop_sim_given                   true
% 1.17/1.05  --inst_prop_sim_new                     false
% 1.17/1.05  --inst_subs_new                         false
% 1.17/1.06  --inst_eq_res_simp                      false
% 1.17/1.06  --inst_subs_given                       false
% 1.17/1.06  --inst_orphan_elimination               true
% 1.17/1.06  --inst_learning_loop_flag               true
% 1.17/1.06  --inst_learning_start                   3000
% 1.17/1.06  --inst_learning_factor                  2
% 1.17/1.06  --inst_start_prop_sim_after_learn       3
% 1.17/1.06  --inst_sel_renew                        solver
% 1.17/1.06  --inst_lit_activity_flag                true
% 1.17/1.06  --inst_restr_to_given                   false
% 1.17/1.06  --inst_activity_threshold               500
% 1.17/1.06  --inst_out_proof                        true
% 1.17/1.06  
% 1.17/1.06  ------ Resolution Options
% 1.17/1.06  
% 1.17/1.06  --resolution_flag                       true
% 1.17/1.06  --res_lit_sel                           adaptive
% 1.17/1.06  --res_lit_sel_side                      none
% 1.17/1.06  --res_ordering                          kbo
% 1.17/1.06  --res_to_prop_solver                    active
% 1.17/1.06  --res_prop_simpl_new                    false
% 1.17/1.06  --res_prop_simpl_given                  true
% 1.17/1.06  --res_passive_queue_type                priority_queues
% 1.17/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/1.06  --res_passive_queues_freq               [15;5]
% 1.17/1.06  --res_forward_subs                      full
% 1.17/1.06  --res_backward_subs                     full
% 1.17/1.06  --res_forward_subs_resolution           true
% 1.17/1.06  --res_backward_subs_resolution          true
% 1.17/1.06  --res_orphan_elimination                true
% 1.17/1.06  --res_time_limit                        2.
% 1.17/1.06  --res_out_proof                         true
% 1.17/1.06  
% 1.17/1.06  ------ Superposition Options
% 1.17/1.06  
% 1.17/1.06  --superposition_flag                    true
% 1.17/1.06  --sup_passive_queue_type                priority_queues
% 1.17/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.17/1.06  --demod_completeness_check              fast
% 1.17/1.06  --demod_use_ground                      true
% 1.17/1.06  --sup_to_prop_solver                    passive
% 1.17/1.06  --sup_prop_simpl_new                    true
% 1.17/1.06  --sup_prop_simpl_given                  true
% 1.17/1.06  --sup_fun_splitting                     false
% 1.17/1.06  --sup_smt_interval                      50000
% 1.17/1.06  
% 1.17/1.06  ------ Superposition Simplification Setup
% 1.17/1.06  
% 1.17/1.06  --sup_indices_passive                   []
% 1.17/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.06  --sup_full_bw                           [BwDemod]
% 1.17/1.06  --sup_immed_triv                        [TrivRules]
% 1.17/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.06  --sup_immed_bw_main                     []
% 1.17/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.06  
% 1.17/1.06  ------ Combination Options
% 1.17/1.06  
% 1.17/1.06  --comb_res_mult                         3
% 1.17/1.06  --comb_sup_mult                         2
% 1.17/1.06  --comb_inst_mult                        10
% 1.17/1.06  
% 1.17/1.06  ------ Debug Options
% 1.17/1.06  
% 1.17/1.06  --dbg_backtrace                         false
% 1.17/1.06  --dbg_dump_prop_clauses                 false
% 1.17/1.06  --dbg_dump_prop_clauses_file            -
% 1.17/1.06  --dbg_out_stat                          false
% 1.17/1.06  ------ Parsing...
% 1.17/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.17/1.06  
% 1.17/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.17/1.06  
% 1.17/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.17/1.06  
% 1.17/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.17/1.06  ------ Proving...
% 1.17/1.06  ------ Problem Properties 
% 1.17/1.06  
% 1.17/1.06  
% 1.17/1.06  clauses                                 13
% 1.17/1.06  conjectures                             5
% 1.17/1.06  EPR                                     2
% 1.17/1.06  Horn                                    13
% 1.17/1.06  unary                                   5
% 1.17/1.06  binary                                  2
% 1.17/1.06  lits                                    34
% 1.17/1.06  lits eq                                 1
% 1.17/1.06  fd_pure                                 0
% 1.17/1.06  fd_pseudo                               0
% 1.17/1.06  fd_cond                                 0
% 1.17/1.06  fd_pseudo_cond                          0
% 1.17/1.06  AC symbols                              0
% 1.17/1.06  
% 1.17/1.06  ------ Schedule dynamic 5 is on 
% 1.17/1.06  
% 1.17/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.17/1.06  
% 1.17/1.06  
% 1.17/1.06  ------ 
% 1.17/1.06  Current options:
% 1.17/1.06  ------ 
% 1.17/1.06  
% 1.17/1.06  ------ Input Options
% 1.17/1.06  
% 1.17/1.06  --out_options                           all
% 1.17/1.06  --tptp_safe_out                         true
% 1.17/1.06  --problem_path                          ""
% 1.17/1.06  --include_path                          ""
% 1.17/1.06  --clausifier                            res/vclausify_rel
% 1.17/1.06  --clausifier_options                    --mode clausify
% 1.17/1.06  --stdin                                 false
% 1.17/1.06  --stats_out                             all
% 1.17/1.06  
% 1.17/1.06  ------ General Options
% 1.17/1.06  
% 1.17/1.06  --fof                                   false
% 1.17/1.06  --time_out_real                         305.
% 1.17/1.06  --time_out_virtual                      -1.
% 1.17/1.06  --symbol_type_check                     false
% 1.17/1.06  --clausify_out                          false
% 1.17/1.06  --sig_cnt_out                           false
% 1.17/1.06  --trig_cnt_out                          false
% 1.17/1.06  --trig_cnt_out_tolerance                1.
% 1.17/1.06  --trig_cnt_out_sk_spl                   false
% 1.17/1.06  --abstr_cl_out                          false
% 1.17/1.06  
% 1.17/1.06  ------ Global Options
% 1.17/1.06  
% 1.17/1.06  --schedule                              default
% 1.17/1.06  --add_important_lit                     false
% 1.17/1.06  --prop_solver_per_cl                    1000
% 1.17/1.06  --min_unsat_core                        false
% 1.17/1.06  --soft_assumptions                      false
% 1.17/1.06  --soft_lemma_size                       3
% 1.17/1.06  --prop_impl_unit_size                   0
% 1.17/1.06  --prop_impl_unit                        []
% 1.17/1.06  --share_sel_clauses                     true
% 1.17/1.06  --reset_solvers                         false
% 1.17/1.06  --bc_imp_inh                            [conj_cone]
% 1.17/1.06  --conj_cone_tolerance                   3.
% 1.17/1.06  --extra_neg_conj                        none
% 1.17/1.06  --large_theory_mode                     true
% 1.17/1.06  --prolific_symb_bound                   200
% 1.17/1.06  --lt_threshold                          2000
% 1.17/1.06  --clause_weak_htbl                      true
% 1.17/1.06  --gc_record_bc_elim                     false
% 1.17/1.06  
% 1.17/1.06  ------ Preprocessing Options
% 1.17/1.06  
% 1.17/1.06  --preprocessing_flag                    true
% 1.17/1.06  --time_out_prep_mult                    0.1
% 1.17/1.06  --splitting_mode                        input
% 1.17/1.06  --splitting_grd                         true
% 1.17/1.06  --splitting_cvd                         false
% 1.17/1.06  --splitting_cvd_svl                     false
% 1.17/1.06  --splitting_nvd                         32
% 1.17/1.06  --sub_typing                            true
% 1.17/1.06  --prep_gs_sim                           true
% 1.17/1.06  --prep_unflatten                        true
% 1.17/1.06  --prep_res_sim                          true
% 1.17/1.06  --prep_upred                            true
% 1.17/1.06  --prep_sem_filter                       exhaustive
% 1.17/1.06  --prep_sem_filter_out                   false
% 1.17/1.06  --pred_elim                             true
% 1.17/1.06  --res_sim_input                         true
% 1.17/1.06  --eq_ax_congr_red                       true
% 1.17/1.06  --pure_diseq_elim                       true
% 1.17/1.06  --brand_transform                       false
% 1.17/1.06  --non_eq_to_eq                          false
% 1.17/1.06  --prep_def_merge                        true
% 1.17/1.06  --prep_def_merge_prop_impl              false
% 1.17/1.06  --prep_def_merge_mbd                    true
% 1.17/1.06  --prep_def_merge_tr_red                 false
% 1.17/1.06  --prep_def_merge_tr_cl                  false
% 1.17/1.06  --smt_preprocessing                     true
% 1.17/1.06  --smt_ac_axioms                         fast
% 1.17/1.06  --preprocessed_out                      false
% 1.17/1.06  --preprocessed_stats                    false
% 1.17/1.06  
% 1.17/1.06  ------ Abstraction refinement Options
% 1.17/1.06  
% 1.17/1.06  --abstr_ref                             []
% 1.17/1.06  --abstr_ref_prep                        false
% 1.17/1.06  --abstr_ref_until_sat                   false
% 1.17/1.06  --abstr_ref_sig_restrict                funpre
% 1.17/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.17/1.06  --abstr_ref_under                       []
% 1.17/1.06  
% 1.17/1.06  ------ SAT Options
% 1.17/1.06  
% 1.17/1.06  --sat_mode                              false
% 1.17/1.06  --sat_fm_restart_options                ""
% 1.17/1.06  --sat_gr_def                            false
% 1.17/1.06  --sat_epr_types                         true
% 1.17/1.06  --sat_non_cyclic_types                  false
% 1.17/1.06  --sat_finite_models                     false
% 1.17/1.06  --sat_fm_lemmas                         false
% 1.17/1.06  --sat_fm_prep                           false
% 1.17/1.06  --sat_fm_uc_incr                        true
% 1.17/1.06  --sat_out_model                         small
% 1.17/1.06  --sat_out_clauses                       false
% 1.17/1.06  
% 1.17/1.06  ------ QBF Options
% 1.17/1.06  
% 1.17/1.06  --qbf_mode                              false
% 1.17/1.06  --qbf_elim_univ                         false
% 1.17/1.06  --qbf_dom_inst                          none
% 1.17/1.06  --qbf_dom_pre_inst                      false
% 1.17/1.06  --qbf_sk_in                             false
% 1.17/1.06  --qbf_pred_elim                         true
% 1.17/1.06  --qbf_split                             512
% 1.17/1.06  
% 1.17/1.06  ------ BMC1 Options
% 1.17/1.06  
% 1.17/1.06  --bmc1_incremental                      false
% 1.17/1.06  --bmc1_axioms                           reachable_all
% 1.17/1.06  --bmc1_min_bound                        0
% 1.17/1.06  --bmc1_max_bound                        -1
% 1.17/1.06  --bmc1_max_bound_default                -1
% 1.17/1.06  --bmc1_symbol_reachability              true
% 1.17/1.06  --bmc1_property_lemmas                  false
% 1.17/1.06  --bmc1_k_induction                      false
% 1.17/1.06  --bmc1_non_equiv_states                 false
% 1.17/1.06  --bmc1_deadlock                         false
% 1.17/1.06  --bmc1_ucm                              false
% 1.17/1.06  --bmc1_add_unsat_core                   none
% 1.17/1.06  --bmc1_unsat_core_children              false
% 1.17/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.17/1.06  --bmc1_out_stat                         full
% 1.17/1.06  --bmc1_ground_init                      false
% 1.17/1.06  --bmc1_pre_inst_next_state              false
% 1.17/1.06  --bmc1_pre_inst_state                   false
% 1.17/1.06  --bmc1_pre_inst_reach_state             false
% 1.17/1.06  --bmc1_out_unsat_core                   false
% 1.17/1.06  --bmc1_aig_witness_out                  false
% 1.17/1.06  --bmc1_verbose                          false
% 1.17/1.06  --bmc1_dump_clauses_tptp                false
% 1.17/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.17/1.06  --bmc1_dump_file                        -
% 1.17/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.17/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.17/1.06  --bmc1_ucm_extend_mode                  1
% 1.17/1.06  --bmc1_ucm_init_mode                    2
% 1.17/1.06  --bmc1_ucm_cone_mode                    none
% 1.17/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.17/1.06  --bmc1_ucm_relax_model                  4
% 1.17/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.17/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.17/1.06  --bmc1_ucm_layered_model                none
% 1.17/1.06  --bmc1_ucm_max_lemma_size               10
% 1.17/1.06  
% 1.17/1.06  ------ AIG Options
% 1.17/1.06  
% 1.17/1.06  --aig_mode                              false
% 1.17/1.06  
% 1.17/1.06  ------ Instantiation Options
% 1.17/1.06  
% 1.17/1.06  --instantiation_flag                    true
% 1.17/1.06  --inst_sos_flag                         false
% 1.17/1.06  --inst_sos_phase                        true
% 1.17/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.17/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.17/1.06  --inst_lit_sel_side                     none
% 1.17/1.06  --inst_solver_per_active                1400
% 1.17/1.06  --inst_solver_calls_frac                1.
% 1.17/1.06  --inst_passive_queue_type               priority_queues
% 1.17/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.17/1.06  --inst_passive_queues_freq              [25;2]
% 1.17/1.06  --inst_dismatching                      true
% 1.17/1.06  --inst_eager_unprocessed_to_passive     true
% 1.17/1.06  --inst_prop_sim_given                   true
% 1.17/1.06  --inst_prop_sim_new                     false
% 1.17/1.06  --inst_subs_new                         false
% 1.17/1.06  --inst_eq_res_simp                      false
% 1.17/1.06  --inst_subs_given                       false
% 1.17/1.06  --inst_orphan_elimination               true
% 1.17/1.06  --inst_learning_loop_flag               true
% 1.17/1.06  --inst_learning_start                   3000
% 1.17/1.06  --inst_learning_factor                  2
% 1.17/1.06  --inst_start_prop_sim_after_learn       3
% 1.17/1.06  --inst_sel_renew                        solver
% 1.17/1.06  --inst_lit_activity_flag                true
% 1.17/1.06  --inst_restr_to_given                   false
% 1.17/1.06  --inst_activity_threshold               500
% 1.17/1.06  --inst_out_proof                        true
% 1.17/1.06  
% 1.17/1.06  ------ Resolution Options
% 1.17/1.06  
% 1.17/1.06  --resolution_flag                       false
% 1.17/1.06  --res_lit_sel                           adaptive
% 1.17/1.06  --res_lit_sel_side                      none
% 1.17/1.06  --res_ordering                          kbo
% 1.17/1.06  --res_to_prop_solver                    active
% 1.17/1.06  --res_prop_simpl_new                    false
% 1.17/1.06  --res_prop_simpl_given                  true
% 1.17/1.06  --res_passive_queue_type                priority_queues
% 1.17/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.17/1.06  --res_passive_queues_freq               [15;5]
% 1.17/1.06  --res_forward_subs                      full
% 1.17/1.06  --res_backward_subs                     full
% 1.17/1.06  --res_forward_subs_resolution           true
% 1.17/1.06  --res_backward_subs_resolution          true
% 1.17/1.06  --res_orphan_elimination                true
% 1.17/1.06  --res_time_limit                        2.
% 1.17/1.06  --res_out_proof                         true
% 1.17/1.06  
% 1.17/1.06  ------ Superposition Options
% 1.17/1.06  
% 1.17/1.06  --superposition_flag                    true
% 1.17/1.06  --sup_passive_queue_type                priority_queues
% 1.17/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.17/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.17/1.06  --demod_completeness_check              fast
% 1.17/1.06  --demod_use_ground                      true
% 1.17/1.06  --sup_to_prop_solver                    passive
% 1.17/1.06  --sup_prop_simpl_new                    true
% 1.17/1.06  --sup_prop_simpl_given                  true
% 1.17/1.06  --sup_fun_splitting                     false
% 1.17/1.06  --sup_smt_interval                      50000
% 1.17/1.06  
% 1.17/1.06  ------ Superposition Simplification Setup
% 1.17/1.06  
% 1.17/1.06  --sup_indices_passive                   []
% 1.17/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.17/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.17/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.06  --sup_full_bw                           [BwDemod]
% 1.17/1.06  --sup_immed_triv                        [TrivRules]
% 1.17/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.17/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.06  --sup_immed_bw_main                     []
% 1.17/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.17/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.17/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.17/1.06  
% 1.17/1.06  ------ Combination Options
% 1.17/1.06  
% 1.17/1.06  --comb_res_mult                         3
% 1.17/1.06  --comb_sup_mult                         2
% 1.17/1.06  --comb_inst_mult                        10
% 1.17/1.06  
% 1.17/1.06  ------ Debug Options
% 1.17/1.06  
% 1.17/1.06  --dbg_backtrace                         false
% 1.17/1.06  --dbg_dump_prop_clauses                 false
% 1.17/1.06  --dbg_dump_prop_clauses_file            -
% 1.17/1.06  --dbg_out_stat                          false
% 1.17/1.06  
% 1.17/1.06  
% 1.17/1.06  
% 1.17/1.06  
% 1.17/1.06  ------ Proving...
% 1.17/1.06  
% 1.17/1.06  
% 1.17/1.06  % SZS status Theorem for theBenchmark.p
% 1.17/1.06  
% 1.17/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 1.17/1.06  
% 1.17/1.06  fof(f8,conjecture,(
% 1.17/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.17/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.06  
% 1.17/1.06  fof(f9,negated_conjecture,(
% 1.17/1.06    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.17/1.06    inference(negated_conjecture,[],[f8])).
% 1.17/1.06  
% 1.17/1.06  fof(f20,plain,(
% 1.17/1.06    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.17/1.06    inference(ennf_transformation,[],[f9])).
% 1.17/1.06  
% 1.17/1.06  fof(f21,plain,(
% 1.17/1.06    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.17/1.06    inference(flattening,[],[f20])).
% 1.17/1.06  
% 1.17/1.06  fof(f25,plain,(
% 1.17/1.06    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.17/1.06    introduced(choice_axiom,[])).
% 1.17/1.06  
% 1.17/1.06  fof(f24,plain,(
% 1.17/1.06    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.17/1.06    introduced(choice_axiom,[])).
% 1.17/1.06  
% 1.17/1.06  fof(f23,plain,(
% 1.17/1.06    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.17/1.06    introduced(choice_axiom,[])).
% 1.17/1.06  
% 1.17/1.06  fof(f26,plain,(
% 1.17/1.06    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.17/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24,f23])).
% 1.17/1.06  
% 1.17/1.06  fof(f38,plain,(
% 1.17/1.06    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.17/1.06    inference(cnf_transformation,[],[f26])).
% 1.17/1.06  
% 1.17/1.06  fof(f5,axiom,(
% 1.17/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k3_xboole_0(X1,X2),X0))),
% 1.17/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.06  
% 1.17/1.06  fof(f14,plain,(
% 1.17/1.06    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.17/1.06    inference(ennf_transformation,[],[f5])).
% 1.17/1.06  
% 1.17/1.06  fof(f15,plain,(
% 1.17/1.06    ! [X0,X1,X2] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.17/1.06    inference(flattening,[],[f14])).
% 1.17/1.06  
% 1.17/1.06  fof(f32,plain,(
% 1.17/1.06    ( ! [X2,X0,X1] : (v4_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.17/1.06    inference(cnf_transformation,[],[f15])).
% 1.17/1.06  
% 1.17/1.06  fof(f36,plain,(
% 1.17/1.06    l1_pre_topc(sK0)),
% 1.17/1.06    inference(cnf_transformation,[],[f26])).
% 1.17/1.06  
% 1.17/1.06  fof(f35,plain,(
% 1.17/1.06    v2_pre_topc(sK0)),
% 1.17/1.06    inference(cnf_transformation,[],[f26])).
% 1.17/1.06  
% 1.17/1.06  fof(f3,axiom,(
% 1.17/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.17/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.06  
% 1.17/1.06  fof(f12,plain,(
% 1.17/1.06    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.17/1.06    inference(ennf_transformation,[],[f3])).
% 1.17/1.06  
% 1.17/1.06  fof(f22,plain,(
% 1.17/1.06    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.17/1.06    inference(nnf_transformation,[],[f12])).
% 1.17/1.06  
% 1.17/1.06  fof(f30,plain,(
% 1.17/1.06    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.17/1.06    inference(cnf_transformation,[],[f22])).
% 1.17/1.06  
% 1.17/1.06  fof(f6,axiom,(
% 1.17/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 1.17/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.06  
% 1.17/1.06  fof(f16,plain,(
% 1.17/1.06    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.17/1.06    inference(ennf_transformation,[],[f6])).
% 1.17/1.06  
% 1.17/1.06  fof(f17,plain,(
% 1.17/1.06    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.17/1.06    inference(flattening,[],[f16])).
% 1.17/1.06  
% 1.17/1.06  fof(f33,plain,(
% 1.17/1.06    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.17/1.06    inference(cnf_transformation,[],[f17])).
% 1.17/1.06  
% 1.17/1.06  fof(f39,plain,(
% 1.17/1.06    v8_pre_topc(sK0)),
% 1.17/1.06    inference(cnf_transformation,[],[f26])).
% 1.17/1.06  
% 1.17/1.06  fof(f4,axiom,(
% 1.17/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 1.17/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.06  
% 1.17/1.06  fof(f13,plain,(
% 1.17/1.06    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.17/1.06    inference(ennf_transformation,[],[f4])).
% 1.17/1.06  
% 1.17/1.06  fof(f31,plain,(
% 1.17/1.06    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.17/1.06    inference(cnf_transformation,[],[f13])).
% 1.17/1.06  
% 1.17/1.06  fof(f2,axiom,(
% 1.17/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.17/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.06  
% 1.17/1.06  fof(f11,plain,(
% 1.17/1.06    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.17/1.06    inference(ennf_transformation,[],[f2])).
% 1.17/1.06  
% 1.17/1.06  fof(f28,plain,(
% 1.17/1.06    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.17/1.06    inference(cnf_transformation,[],[f11])).
% 1.17/1.06  
% 1.17/1.06  fof(f1,axiom,(
% 1.17/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.17/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.06  
% 1.17/1.06  fof(f10,plain,(
% 1.17/1.06    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.17/1.06    inference(ennf_transformation,[],[f1])).
% 1.17/1.06  
% 1.17/1.06  fof(f27,plain,(
% 1.17/1.06    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.17/1.06    inference(cnf_transformation,[],[f10])).
% 1.17/1.06  
% 1.17/1.06  fof(f7,axiom,(
% 1.17/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 1.17/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.17/1.06  
% 1.17/1.06  fof(f18,plain,(
% 1.17/1.06    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.17/1.06    inference(ennf_transformation,[],[f7])).
% 1.17/1.06  
% 1.17/1.06  fof(f19,plain,(
% 1.17/1.06    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.17/1.06    inference(flattening,[],[f18])).
% 1.17/1.06  
% 1.17/1.06  fof(f34,plain,(
% 1.17/1.06    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.17/1.06    inference(cnf_transformation,[],[f19])).
% 1.17/1.06  
% 1.17/1.06  fof(f42,plain,(
% 1.17/1.06    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.17/1.06    inference(cnf_transformation,[],[f26])).
% 1.17/1.06  
% 1.17/1.06  fof(f41,plain,(
% 1.17/1.06    v2_compts_1(sK2,sK0)),
% 1.17/1.06    inference(cnf_transformation,[],[f26])).
% 1.17/1.06  
% 1.17/1.06  fof(f40,plain,(
% 1.17/1.06    v2_compts_1(sK1,sK0)),
% 1.17/1.06    inference(cnf_transformation,[],[f26])).
% 1.17/1.06  
% 1.17/1.06  fof(f37,plain,(
% 1.17/1.06    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.17/1.06    inference(cnf_transformation,[],[f26])).
% 1.17/1.06  
% 1.17/1.06  cnf(c_12,negated_conjecture,
% 1.17/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(cnf_transformation,[],[f38]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_360,negated_conjecture,
% 1.17/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(subtyping,[status(esa)],[c_12]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_646,plain,
% 1.17/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_5,plain,
% 1.17/1.06      ( ~ v4_pre_topc(X0,X1)
% 1.17/1.06      | ~ v4_pre_topc(X2,X1)
% 1.17/1.06      | v4_pre_topc(k3_xboole_0(X2,X0),X1)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.06      | ~ v2_pre_topc(X1)
% 1.17/1.06      | ~ l1_pre_topc(X1) ),
% 1.17/1.06      inference(cnf_transformation,[],[f32]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_14,negated_conjecture,
% 1.17/1.06      ( l1_pre_topc(sK0) ),
% 1.17/1.06      inference(cnf_transformation,[],[f36]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_225,plain,
% 1.17/1.06      ( ~ v4_pre_topc(X0,X1)
% 1.17/1.06      | ~ v4_pre_topc(X2,X1)
% 1.17/1.06      | v4_pre_topc(k3_xboole_0(X2,X0),X1)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.06      | ~ v2_pre_topc(X1)
% 1.17/1.06      | sK0 != X1 ),
% 1.17/1.06      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_226,plain,
% 1.17/1.06      ( ~ v4_pre_topc(X0,sK0)
% 1.17/1.06      | ~ v4_pre_topc(X1,sK0)
% 1.17/1.06      | v4_pre_topc(k3_xboole_0(X1,X0),sK0)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ v2_pre_topc(sK0) ),
% 1.17/1.06      inference(unflattening,[status(thm)],[c_225]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_15,negated_conjecture,
% 1.17/1.06      ( v2_pre_topc(sK0) ),
% 1.17/1.06      inference(cnf_transformation,[],[f35]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_230,plain,
% 1.17/1.06      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | v4_pre_topc(k3_xboole_0(X1,X0),sK0)
% 1.17/1.06      | ~ v4_pre_topc(X1,sK0)
% 1.17/1.06      | ~ v4_pre_topc(X0,sK0) ),
% 1.17/1.06      inference(global_propositional_subsumption,
% 1.17/1.06                [status(thm)],
% 1.17/1.06                [c_226,c_15]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_231,plain,
% 1.17/1.06      ( ~ v4_pre_topc(X0,sK0)
% 1.17/1.06      | ~ v4_pre_topc(X1,sK0)
% 1.17/1.06      | v4_pre_topc(k3_xboole_0(X1,X0),sK0)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(renaming,[status(thm)],[c_230]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_356,plain,
% 1.17/1.06      ( ~ v4_pre_topc(X0_43,sK0)
% 1.17/1.06      | ~ v4_pre_topc(X1_43,sK0)
% 1.17/1.06      | v4_pre_topc(k3_xboole_0(X1_43,X0_43),sK0)
% 1.17/1.06      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(subtyping,[status(esa)],[c_231]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_650,plain,
% 1.17/1.06      ( v4_pre_topc(X0_43,sK0) != iProver_top
% 1.17/1.06      | v4_pre_topc(X1_43,sK0) != iProver_top
% 1.17/1.06      | v4_pre_topc(k3_xboole_0(X1_43,X0_43),sK0) = iProver_top
% 1.17/1.06      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.17/1.06      | m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_1807,plain,
% 1.17/1.06      ( v4_pre_topc(X0_43,sK0) != iProver_top
% 1.17/1.06      | v4_pre_topc(k3_xboole_0(X0_43,sK2),sK0) = iProver_top
% 1.17/1.06      | v4_pre_topc(sK2,sK0) != iProver_top
% 1.17/1.06      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(superposition,[status(thm)],[c_646,c_650]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_1837,plain,
% 1.17/1.06      ( v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) = iProver_top
% 1.17/1.06      | v4_pre_topc(sK2,sK0) != iProver_top
% 1.17/1.06      | v4_pre_topc(sK1,sK0) != iProver_top
% 1.17/1.06      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_1807]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_376,plain,
% 1.17/1.06      ( ~ v4_pre_topc(X0_43,X0_44)
% 1.17/1.06      | v4_pre_topc(X1_43,X0_44)
% 1.17/1.06      | X1_43 != X0_43 ),
% 1.17/1.06      theory(equality) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_910,plain,
% 1.17/1.06      ( ~ v4_pre_topc(X0_43,sK0)
% 1.17/1.06      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 1.17/1.06      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_43 ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_376]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_1372,plain,
% 1.17/1.06      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 1.17/1.06      | ~ v4_pre_topc(k3_xboole_0(sK1,sK2),sK0)
% 1.17/1.06      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2) ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_910]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_1373,plain,
% 1.17/1.06      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2)
% 1.17/1.06      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
% 1.17/1.06      | v4_pre_topc(k3_xboole_0(sK1,sK2),sK0) != iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_1372]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_2,plain,
% 1.17/1.06      ( r1_tarski(X0,X1)
% 1.17/1.06      | ~ r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
% 1.17/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ),
% 1.17/1.06      inference(cnf_transformation,[],[f30]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_366,plain,
% 1.17/1.06      ( r1_tarski(X0_43,X1_43)
% 1.17/1.06      | ~ r1_tarski(k3_subset_1(X0_46,X1_43),k3_subset_1(X0_46,X0_43))
% 1.17/1.06      | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_46))
% 1.17/1.06      | ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_46)) ),
% 1.17/1.06      inference(subtyping,[status(esa)],[c_2]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_804,plain,
% 1.17/1.06      ( r1_tarski(X0_43,sK1)
% 1.17/1.06      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),X0_43))
% 1.17/1.06      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_366]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_965,plain,
% 1.17/1.06      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 1.17/1.06      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 1.17/1.06      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_804]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_967,plain,
% 1.17/1.06      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) = iProver_top
% 1.17/1.06      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top
% 1.17/1.06      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.17/1.06      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_965]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_6,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0,X1)
% 1.17/1.06      | v4_pre_topc(X0,X1)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.06      | ~ v8_pre_topc(X1)
% 1.17/1.06      | ~ v2_pre_topc(X1)
% 1.17/1.06      | ~ l1_pre_topc(X1) ),
% 1.17/1.06      inference(cnf_transformation,[],[f33]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_11,negated_conjecture,
% 1.17/1.06      ( v8_pre_topc(sK0) ),
% 1.17/1.06      inference(cnf_transformation,[],[f39]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_174,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0,X1)
% 1.17/1.06      | v4_pre_topc(X0,X1)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.06      | ~ v2_pre_topc(X1)
% 1.17/1.06      | ~ l1_pre_topc(X1)
% 1.17/1.06      | sK0 != X1 ),
% 1.17/1.06      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_175,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0,sK0)
% 1.17/1.06      | v4_pre_topc(X0,sK0)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ v2_pre_topc(sK0)
% 1.17/1.06      | ~ l1_pre_topc(sK0) ),
% 1.17/1.06      inference(unflattening,[status(thm)],[c_174]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_179,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0,sK0)
% 1.17/1.06      | v4_pre_topc(X0,sK0)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(global_propositional_subsumption,
% 1.17/1.06                [status(thm)],
% 1.17/1.06                [c_175,c_15,c_14]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_358,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0_43,sK0)
% 1.17/1.06      | v4_pre_topc(X0_43,sK0)
% 1.17/1.06      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(subtyping,[status(esa)],[c_179]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_648,plain,
% 1.17/1.06      ( v2_compts_1(X0_43,sK0) != iProver_top
% 1.17/1.06      | v4_pre_topc(X0_43,sK0) = iProver_top
% 1.17/1.06      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_921,plain,
% 1.17/1.06      ( v2_compts_1(sK2,sK0) != iProver_top
% 1.17/1.06      | v4_pre_topc(sK2,sK0) = iProver_top ),
% 1.17/1.06      inference(superposition,[status(thm)],[c_646,c_648]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_4,plain,
% 1.17/1.06      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
% 1.17/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 1.17/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
% 1.17/1.06      inference(cnf_transformation,[],[f31]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_364,plain,
% 1.17/1.06      ( r1_tarski(k3_subset_1(X0_46,X0_43),k3_subset_1(X0_46,k9_subset_1(X0_46,X0_43,X1_43)))
% 1.17/1.06      | ~ m1_subset_1(X1_43,k1_zfmisc_1(X0_46))
% 1.17/1.06      | ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_46)) ),
% 1.17/1.06      inference(subtyping,[status(esa)],[c_4]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_789,plain,
% 1.17/1.06      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_43),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_43,sK2)))
% 1.17/1.06      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_364]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_790,plain,
% 1.17/1.06      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),X0_43),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_43,sK2))) = iProver_top
% 1.17/1.06      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.17/1.06      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_792,plain,
% 1.17/1.06      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))) = iProver_top
% 1.17/1.06      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.17/1.06      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_790]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_1,plain,
% 1.17/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.17/1.06      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 1.17/1.06      inference(cnf_transformation,[],[f28]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_367,plain,
% 1.17/1.06      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_46))
% 1.17/1.06      | k9_subset_1(X0_46,X1_43,X0_43) = k3_xboole_0(X1_43,X0_43) ),
% 1.17/1.06      inference(subtyping,[status(esa)],[c_1]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_779,plain,
% 1.17/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | k9_subset_1(u1_struct_0(sK0),X0_43,sK2) = k3_xboole_0(X0_43,sK2) ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_367]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_781,plain,
% 1.17/1.06      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_779]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_0,plain,
% 1.17/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.17/1.06      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 1.17/1.06      inference(cnf_transformation,[],[f27]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_368,plain,
% 1.17/1.06      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X0_46))
% 1.17/1.06      | m1_subset_1(k9_subset_1(X0_46,X1_43,X0_43),k1_zfmisc_1(X0_46)) ),
% 1.17/1.06      inference(subtyping,[status(esa)],[c_0]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_754,plain,
% 1.17/1.06      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_43,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_368]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_755,plain,
% 1.17/1.06      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_43,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 1.17/1.06      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_757,plain,
% 1.17/1.06      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 1.17/1.06      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_755]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_7,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0,X1)
% 1.17/1.06      | v2_compts_1(X2,X1)
% 1.17/1.06      | ~ v4_pre_topc(X2,X1)
% 1.17/1.06      | ~ r1_tarski(X2,X0)
% 1.17/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.06      | ~ v2_pre_topc(X1)
% 1.17/1.06      | ~ l1_pre_topc(X1) ),
% 1.17/1.06      inference(cnf_transformation,[],[f34]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_199,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0,X1)
% 1.17/1.06      | v2_compts_1(X2,X1)
% 1.17/1.06      | ~ v4_pre_topc(X2,X1)
% 1.17/1.06      | ~ r1_tarski(X2,X0)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.17/1.06      | ~ v2_pre_topc(X1)
% 1.17/1.06      | sK0 != X1 ),
% 1.17/1.06      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_200,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0,sK0)
% 1.17/1.06      | v2_compts_1(X1,sK0)
% 1.17/1.06      | ~ v4_pre_topc(X1,sK0)
% 1.17/1.06      | ~ r1_tarski(X1,X0)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ v2_pre_topc(sK0) ),
% 1.17/1.06      inference(unflattening,[status(thm)],[c_199]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_202,plain,
% 1.17/1.06      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ r1_tarski(X1,X0)
% 1.17/1.06      | ~ v4_pre_topc(X1,sK0)
% 1.17/1.06      | v2_compts_1(X1,sK0)
% 1.17/1.06      | ~ v2_compts_1(X0,sK0) ),
% 1.17/1.06      inference(global_propositional_subsumption,
% 1.17/1.06                [status(thm)],
% 1.17/1.06                [c_200,c_15]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_203,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0,sK0)
% 1.17/1.06      | v2_compts_1(X1,sK0)
% 1.17/1.06      | ~ v4_pre_topc(X1,sK0)
% 1.17/1.06      | ~ r1_tarski(X1,X0)
% 1.17/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(renaming,[status(thm)],[c_202]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_357,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0_43,sK0)
% 1.17/1.06      | v2_compts_1(X1_43,sK0)
% 1.17/1.06      | ~ v4_pre_topc(X1_43,sK0)
% 1.17/1.06      | ~ r1_tarski(X1_43,X0_43)
% 1.17/1.06      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(X1_43,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(subtyping,[status(esa)],[c_203]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_749,plain,
% 1.17/1.06      ( ~ v2_compts_1(X0_43,sK0)
% 1.17/1.06      | v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 1.17/1.06      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 1.17/1.06      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0_43)
% 1.17/1.06      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.17/1.06      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_357]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_750,plain,
% 1.17/1.06      ( v2_compts_1(X0_43,sK0) != iProver_top
% 1.17/1.06      | v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
% 1.17/1.06      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top
% 1.17/1.06      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0_43) != iProver_top
% 1.17/1.06      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.17/1.06      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_752,plain,
% 1.17/1.06      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) = iProver_top
% 1.17/1.06      | v2_compts_1(sK1,sK0) != iProver_top
% 1.17/1.06      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top
% 1.17/1.06      | r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) != iProver_top
% 1.17/1.06      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.17/1.06      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_750]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_406,plain,
% 1.17/1.06      ( v2_compts_1(X0_43,sK0) != iProver_top
% 1.17/1.06      | v4_pre_topc(X0_43,sK0) = iProver_top
% 1.17/1.06      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_408,plain,
% 1.17/1.06      ( v2_compts_1(sK1,sK0) != iProver_top
% 1.17/1.06      | v4_pre_topc(sK1,sK0) = iProver_top
% 1.17/1.06      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.17/1.06      inference(instantiation,[status(thm)],[c_406]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_8,negated_conjecture,
% 1.17/1.06      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 1.17/1.06      inference(cnf_transformation,[],[f42]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_23,plain,
% 1.17/1.06      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) != iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_9,negated_conjecture,
% 1.17/1.06      ( v2_compts_1(sK2,sK0) ),
% 1.17/1.06      inference(cnf_transformation,[],[f41]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_22,plain,
% 1.17/1.06      ( v2_compts_1(sK2,sK0) = iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_10,negated_conjecture,
% 1.17/1.06      ( v2_compts_1(sK1,sK0) ),
% 1.17/1.06      inference(cnf_transformation,[],[f40]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_21,plain,
% 1.17/1.06      ( v2_compts_1(sK1,sK0) = iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_19,plain,
% 1.17/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_13,negated_conjecture,
% 1.17/1.06      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.17/1.06      inference(cnf_transformation,[],[f37]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(c_18,plain,
% 1.17/1.06      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.17/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.17/1.06  
% 1.17/1.06  cnf(contradiction,plain,
% 1.17/1.06      ( $false ),
% 1.17/1.06      inference(minisat,
% 1.17/1.06                [status(thm)],
% 1.17/1.06                [c_1837,c_1373,c_967,c_921,c_792,c_781,c_757,c_752,c_408,
% 1.17/1.06                 c_23,c_22,c_21,c_19,c_12,c_18]) ).
% 1.17/1.06  
% 1.17/1.06  
% 1.17/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.17/1.06  
% 1.17/1.06  ------                               Statistics
% 1.17/1.06  
% 1.17/1.06  ------ General
% 1.17/1.06  
% 1.17/1.06  abstr_ref_over_cycles:                  0
% 1.17/1.06  abstr_ref_under_cycles:                 0
% 1.17/1.06  gc_basic_clause_elim:                   0
% 1.17/1.06  forced_gc_time:                         0
% 1.17/1.06  parsing_time:                           0.006
% 1.17/1.06  unif_index_cands_time:                  0.
% 1.17/1.06  unif_index_add_time:                    0.
% 1.17/1.06  orderings_time:                         0.
% 1.17/1.06  out_proof_time:                         0.008
% 1.17/1.06  total_time:                             0.088
% 1.17/1.06  num_of_symbols:                         50
% 1.17/1.06  num_of_terms:                           2355
% 1.17/1.06  
% 1.17/1.06  ------ Preprocessing
% 1.17/1.06  
% 1.17/1.06  num_of_splits:                          0
% 1.17/1.06  num_of_split_atoms:                     0
% 1.17/1.06  num_of_reused_defs:                     0
% 1.17/1.06  num_eq_ax_congr_red:                    16
% 1.17/1.06  num_of_sem_filtered_clauses:            1
% 1.17/1.06  num_of_subtypes:                        4
% 1.17/1.06  monotx_restored_types:                  0
% 1.17/1.06  sat_num_of_epr_types:                   0
% 1.17/1.06  sat_num_of_non_cyclic_types:            0
% 1.17/1.06  sat_guarded_non_collapsed_types:        0
% 1.17/1.06  num_pure_diseq_elim:                    0
% 1.17/1.06  simp_replaced_by:                       0
% 1.17/1.06  res_preprocessed:                       72
% 1.17/1.06  prep_upred:                             0
% 1.17/1.06  prep_unflattend:                        3
% 1.17/1.06  smt_new_axioms:                         0
% 1.17/1.06  pred_elim_cands:                        4
% 1.17/1.06  pred_elim:                              3
% 1.17/1.06  pred_elim_cl:                           3
% 1.17/1.06  pred_elim_cycles:                       5
% 1.17/1.06  merged_defs:                            0
% 1.17/1.06  merged_defs_ncl:                        0
% 1.17/1.06  bin_hyper_res:                          0
% 1.17/1.06  prep_cycles:                            4
% 1.17/1.06  pred_elim_time:                         0.002
% 1.17/1.06  splitting_time:                         0.
% 1.17/1.06  sem_filter_time:                        0.
% 1.17/1.06  monotx_time:                            0.
% 1.17/1.06  subtype_inf_time:                       0.
% 1.17/1.06  
% 1.17/1.06  ------ Problem properties
% 1.17/1.06  
% 1.17/1.06  clauses:                                13
% 1.17/1.06  conjectures:                            5
% 1.17/1.06  epr:                                    2
% 1.17/1.06  horn:                                   13
% 1.17/1.06  ground:                                 5
% 1.17/1.06  unary:                                  5
% 1.17/1.06  binary:                                 2
% 1.17/1.06  lits:                                   34
% 1.17/1.06  lits_eq:                                1
% 1.17/1.06  fd_pure:                                0
% 1.17/1.06  fd_pseudo:                              0
% 1.17/1.06  fd_cond:                                0
% 1.17/1.06  fd_pseudo_cond:                         0
% 1.17/1.06  ac_symbols:                             0
% 1.17/1.06  
% 1.17/1.06  ------ Propositional Solver
% 1.17/1.06  
% 1.17/1.06  prop_solver_calls:                      24
% 1.17/1.06  prop_fast_solver_calls:                 451
% 1.17/1.06  smt_solver_calls:                       0
% 1.17/1.06  smt_fast_solver_calls:                  0
% 1.17/1.06  prop_num_of_clauses:                    700
% 1.17/1.06  prop_preprocess_simplified:             2719
% 1.17/1.06  prop_fo_subsumed:                       6
% 1.17/1.06  prop_solver_time:                       0.
% 1.17/1.06  smt_solver_time:                        0.
% 1.17/1.06  smt_fast_solver_time:                   0.
% 1.17/1.06  prop_fast_solver_time:                  0.
% 1.17/1.06  prop_unsat_core_time:                   0.
% 1.17/1.06  
% 1.17/1.06  ------ QBF
% 1.17/1.06  
% 1.17/1.06  qbf_q_res:                              0
% 1.17/1.06  qbf_num_tautologies:                    0
% 1.17/1.06  qbf_prep_cycles:                        0
% 1.17/1.06  
% 1.17/1.06  ------ BMC1
% 1.17/1.06  
% 1.17/1.06  bmc1_current_bound:                     -1
% 1.17/1.06  bmc1_last_solved_bound:                 -1
% 1.17/1.06  bmc1_unsat_core_size:                   -1
% 1.17/1.06  bmc1_unsat_core_parents_size:           -1
% 1.17/1.06  bmc1_merge_next_fun:                    0
% 1.17/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.17/1.06  
% 1.17/1.06  ------ Instantiation
% 1.17/1.06  
% 1.17/1.06  inst_num_of_clauses:                    190
% 1.17/1.06  inst_num_in_passive:                    15
% 1.17/1.06  inst_num_in_active:                     89
% 1.17/1.06  inst_num_in_unprocessed:                92
% 1.17/1.06  inst_num_of_loops:                      90
% 1.17/1.06  inst_num_of_learning_restarts:          0
% 1.17/1.06  inst_num_moves_active_passive:          0
% 1.17/1.06  inst_lit_activity:                      0
% 1.17/1.06  inst_lit_activity_moves:                0
% 1.17/1.06  inst_num_tautologies:                   0
% 1.17/1.06  inst_num_prop_implied:                  0
% 1.17/1.06  inst_num_existing_simplified:           0
% 1.17/1.06  inst_num_eq_res_simplified:             0
% 1.17/1.06  inst_num_child_elim:                    0
% 1.17/1.06  inst_num_of_dismatching_blockings:      49
% 1.17/1.06  inst_num_of_non_proper_insts:           144
% 1.17/1.06  inst_num_of_duplicates:                 0
% 1.17/1.06  inst_inst_num_from_inst_to_res:         0
% 1.17/1.06  inst_dismatching_checking_time:         0.
% 1.17/1.06  
% 1.17/1.06  ------ Resolution
% 1.17/1.06  
% 1.17/1.06  res_num_of_clauses:                     0
% 1.17/1.06  res_num_in_passive:                     0
% 1.17/1.06  res_num_in_active:                      0
% 1.17/1.06  res_num_of_loops:                       76
% 1.17/1.06  res_forward_subset_subsumed:            2
% 1.17/1.06  res_backward_subset_subsumed:           12
% 1.17/1.06  res_forward_subsumed:                   0
% 1.17/1.06  res_backward_subsumed:                  0
% 1.17/1.06  res_forward_subsumption_resolution:     0
% 1.17/1.06  res_backward_subsumption_resolution:    0
% 1.17/1.06  res_clause_to_clause_subsumption:       32
% 1.17/1.06  res_orphan_elimination:                 0
% 1.17/1.06  res_tautology_del:                      1
% 1.17/1.06  res_num_eq_res_simplified:              0
% 1.17/1.06  res_num_sel_changes:                    0
% 1.17/1.06  res_moves_from_active_to_pass:          0
% 1.17/1.06  
% 1.17/1.06  ------ Superposition
% 1.17/1.06  
% 1.17/1.06  sup_time_total:                         0.
% 1.17/1.06  sup_time_generating:                    0.
% 1.17/1.06  sup_time_sim_full:                      0.
% 1.17/1.06  sup_time_sim_immed:                     0.
% 1.17/1.06  
% 1.17/1.06  sup_num_of_clauses:                     26
% 1.17/1.06  sup_num_in_active:                      16
% 1.17/1.06  sup_num_in_passive:                     10
% 1.17/1.06  sup_num_of_loops:                       16
% 1.17/1.06  sup_fw_superposition:                   9
% 1.17/1.06  sup_bw_superposition:                   6
% 1.17/1.06  sup_immediate_simplified:               0
% 1.17/1.06  sup_given_eliminated:                   0
% 1.17/1.06  comparisons_done:                       0
% 1.17/1.06  comparisons_avoided:                    0
% 1.17/1.06  
% 1.17/1.06  ------ Simplifications
% 1.17/1.06  
% 1.17/1.06  
% 1.17/1.06  sim_fw_subset_subsumed:                 0
% 1.17/1.06  sim_bw_subset_subsumed:                 0
% 1.17/1.06  sim_fw_subsumed:                        0
% 1.17/1.06  sim_bw_subsumed:                        0
% 1.17/1.06  sim_fw_subsumption_res:                 0
% 1.17/1.06  sim_bw_subsumption_res:                 0
% 1.17/1.06  sim_tautology_del:                      0
% 1.17/1.06  sim_eq_tautology_del:                   0
% 1.17/1.06  sim_eq_res_simp:                        0
% 1.17/1.06  sim_fw_demodulated:                     0
% 1.17/1.06  sim_bw_demodulated:                     1
% 1.17/1.06  sim_light_normalised:                   0
% 1.17/1.06  sim_joinable_taut:                      0
% 1.17/1.06  sim_joinable_simp:                      0
% 1.17/1.06  sim_ac_normalised:                      0
% 1.17/1.06  sim_smt_subsumption:                    0
% 1.17/1.06  
%------------------------------------------------------------------------------
