%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:36 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 390 expanded)
%              Number of clauses        :   69 ( 129 expanded)
%              Number of leaves         :   12 ( 108 expanded)
%              Depth                    :   23
%              Number of atoms          :  310 (1747 expanded)
%              Number of equality atoms :   87 ( 143 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X1,X0)
                 => r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)))
        & v3_pre_topc(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k9_subset_1(u1_struct_0(X0),sK1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)))
            & v3_pre_topc(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
                & v3_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)))
              & v3_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31,f30,f29])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

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

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_481,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_741,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k9_subset_1(X1_44,X0_44,X2_44) = k9_subset_1(X1_44,X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_734,plain,
    ( k9_subset_1(X0_44,X1_44,X2_44) = k9_subset_1(X0_44,X2_44,X1_44)
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_1129,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_44,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0_44) ),
    inference(superposition,[status(thm)],[c_741,c_734])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_480,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_742,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_1130,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_44,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0_44) ),
    inference(superposition,[status(thm)],[c_742,c_734])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_16])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_44),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_336])).

cnf(c_744,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_44),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_736,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
    | k9_subset_1(X1_44,X2_44,k3_subset_1(X1_44,X0_44)) = k7_subset_1(X1_44,X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_739,plain,
    ( k9_subset_1(X0_44,X1_44,k3_subset_1(X0_44,X2_44)) = k7_subset_1(X0_44,X1_44,X2_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_1631,plain,
    ( k9_subset_1(X0_44,X1_44,k3_subset_1(X0_44,k3_subset_1(X0_44,X2_44))) = k7_subset_1(X0_44,X1_44,k3_subset_1(X0_44,X2_44))
    | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_739])).

cnf(c_8810,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = k7_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK1))
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_742,c_1631])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k3_subset_1(X1_44,k3_subset_1(X1_44,X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_737,plain,
    ( k3_subset_1(X0_44,k3_subset_1(X0_44,X1_44)) = X1_44
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_1286,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_742,c_737])).

cnf(c_8833,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),X0_44,sK1)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8810,c_1286])).

cnf(c_9341,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),sK1)
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_744,c_8833])).

cnf(c_12117,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_741,c_9341])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_320,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_321,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_10,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,negated_conjecture,
    ( v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_307,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_308,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_310,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_16,c_15])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0
    | k3_subset_1(u1_struct_0(sK0),sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_321,c_310])).

cnf(c_356,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_477,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_745,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_821,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_969,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_15,c_477,c_821])).

cnf(c_11,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_235,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_236,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_236,c_16])).

cnf(c_241,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_479,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k2_pre_topc(sK0,X1_44)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0_44,X1_44)))
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_241])).

cnf(c_743,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k2_pre_topc(sK0,X1_44)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0_44,X1_44))) = iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_974,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_969,c_743])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_822,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_1083,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_974,c_20,c_822])).

cnf(c_1084,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1083])).

cnf(c_12203,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12117,c_1084])).

cnf(c_9339,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(superposition,[status(thm)],[c_741,c_8833])).

cnf(c_12209,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12203,c_9339])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12901,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12209,c_21])).

cnf(c_12906,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_12901])).

cnf(c_12918,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_12906])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12918,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:01:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.01/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/0.98  
% 4.01/0.98  ------  iProver source info
% 4.01/0.98  
% 4.01/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.01/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/0.98  git: non_committed_changes: false
% 4.01/0.98  git: last_make_outside_of_git: false
% 4.01/0.98  
% 4.01/0.98  ------ 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options
% 4.01/0.98  
% 4.01/0.98  --out_options                           all
% 4.01/0.98  --tptp_safe_out                         true
% 4.01/0.98  --problem_path                          ""
% 4.01/0.98  --include_path                          ""
% 4.01/0.98  --clausifier                            res/vclausify_rel
% 4.01/0.98  --clausifier_options                    --mode clausify
% 4.01/0.98  --stdin                                 false
% 4.01/0.98  --stats_out                             all
% 4.01/0.98  
% 4.01/0.98  ------ General Options
% 4.01/0.98  
% 4.01/0.98  --fof                                   false
% 4.01/0.98  --time_out_real                         305.
% 4.01/0.98  --time_out_virtual                      -1.
% 4.01/0.98  --symbol_type_check                     false
% 4.01/0.98  --clausify_out                          false
% 4.01/0.98  --sig_cnt_out                           false
% 4.01/0.98  --trig_cnt_out                          false
% 4.01/0.98  --trig_cnt_out_tolerance                1.
% 4.01/0.98  --trig_cnt_out_sk_spl                   false
% 4.01/0.98  --abstr_cl_out                          false
% 4.01/0.98  
% 4.01/0.98  ------ Global Options
% 4.01/0.98  
% 4.01/0.98  --schedule                              default
% 4.01/0.98  --add_important_lit                     false
% 4.01/0.98  --prop_solver_per_cl                    1000
% 4.01/0.98  --min_unsat_core                        false
% 4.01/0.98  --soft_assumptions                      false
% 4.01/0.98  --soft_lemma_size                       3
% 4.01/0.98  --prop_impl_unit_size                   0
% 4.01/0.98  --prop_impl_unit                        []
% 4.01/0.98  --share_sel_clauses                     true
% 4.01/0.98  --reset_solvers                         false
% 4.01/0.98  --bc_imp_inh                            [conj_cone]
% 4.01/0.98  --conj_cone_tolerance                   3.
% 4.01/0.98  --extra_neg_conj                        none
% 4.01/0.98  --large_theory_mode                     true
% 4.01/0.98  --prolific_symb_bound                   200
% 4.01/0.98  --lt_threshold                          2000
% 4.01/0.98  --clause_weak_htbl                      true
% 4.01/0.98  --gc_record_bc_elim                     false
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing Options
% 4.01/0.98  
% 4.01/0.98  --preprocessing_flag                    true
% 4.01/0.98  --time_out_prep_mult                    0.1
% 4.01/0.98  --splitting_mode                        input
% 4.01/0.98  --splitting_grd                         true
% 4.01/0.98  --splitting_cvd                         false
% 4.01/0.98  --splitting_cvd_svl                     false
% 4.01/0.98  --splitting_nvd                         32
% 4.01/0.98  --sub_typing                            true
% 4.01/0.98  --prep_gs_sim                           true
% 4.01/0.98  --prep_unflatten                        true
% 4.01/0.98  --prep_res_sim                          true
% 4.01/0.98  --prep_upred                            true
% 4.01/0.98  --prep_sem_filter                       exhaustive
% 4.01/0.98  --prep_sem_filter_out                   false
% 4.01/0.98  --pred_elim                             true
% 4.01/0.98  --res_sim_input                         true
% 4.01/0.98  --eq_ax_congr_red                       true
% 4.01/0.98  --pure_diseq_elim                       true
% 4.01/0.98  --brand_transform                       false
% 4.01/0.98  --non_eq_to_eq                          false
% 4.01/0.98  --prep_def_merge                        true
% 4.01/0.98  --prep_def_merge_prop_impl              false
% 4.01/0.98  --prep_def_merge_mbd                    true
% 4.01/0.98  --prep_def_merge_tr_red                 false
% 4.01/0.98  --prep_def_merge_tr_cl                  false
% 4.01/0.98  --smt_preprocessing                     true
% 4.01/0.98  --smt_ac_axioms                         fast
% 4.01/0.98  --preprocessed_out                      false
% 4.01/0.98  --preprocessed_stats                    false
% 4.01/0.98  
% 4.01/0.98  ------ Abstraction refinement Options
% 4.01/0.98  
% 4.01/0.98  --abstr_ref                             []
% 4.01/0.98  --abstr_ref_prep                        false
% 4.01/0.98  --abstr_ref_until_sat                   false
% 4.01/0.98  --abstr_ref_sig_restrict                funpre
% 4.01/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/0.98  --abstr_ref_under                       []
% 4.01/0.98  
% 4.01/0.98  ------ SAT Options
% 4.01/0.98  
% 4.01/0.98  --sat_mode                              false
% 4.01/0.98  --sat_fm_restart_options                ""
% 4.01/0.98  --sat_gr_def                            false
% 4.01/0.98  --sat_epr_types                         true
% 4.01/0.98  --sat_non_cyclic_types                  false
% 4.01/0.98  --sat_finite_models                     false
% 4.01/0.98  --sat_fm_lemmas                         false
% 4.01/0.98  --sat_fm_prep                           false
% 4.01/0.98  --sat_fm_uc_incr                        true
% 4.01/0.98  --sat_out_model                         small
% 4.01/0.98  --sat_out_clauses                       false
% 4.01/0.98  
% 4.01/0.98  ------ QBF Options
% 4.01/0.98  
% 4.01/0.98  --qbf_mode                              false
% 4.01/0.98  --qbf_elim_univ                         false
% 4.01/0.98  --qbf_dom_inst                          none
% 4.01/0.98  --qbf_dom_pre_inst                      false
% 4.01/0.98  --qbf_sk_in                             false
% 4.01/0.98  --qbf_pred_elim                         true
% 4.01/0.98  --qbf_split                             512
% 4.01/0.98  
% 4.01/0.98  ------ BMC1 Options
% 4.01/0.98  
% 4.01/0.98  --bmc1_incremental                      false
% 4.01/0.98  --bmc1_axioms                           reachable_all
% 4.01/0.98  --bmc1_min_bound                        0
% 4.01/0.98  --bmc1_max_bound                        -1
% 4.01/0.98  --bmc1_max_bound_default                -1
% 4.01/0.98  --bmc1_symbol_reachability              true
% 4.01/0.98  --bmc1_property_lemmas                  false
% 4.01/0.98  --bmc1_k_induction                      false
% 4.01/0.98  --bmc1_non_equiv_states                 false
% 4.01/0.98  --bmc1_deadlock                         false
% 4.01/0.98  --bmc1_ucm                              false
% 4.01/0.98  --bmc1_add_unsat_core                   none
% 4.01/0.98  --bmc1_unsat_core_children              false
% 4.01/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/0.98  --bmc1_out_stat                         full
% 4.01/0.98  --bmc1_ground_init                      false
% 4.01/0.98  --bmc1_pre_inst_next_state              false
% 4.01/0.98  --bmc1_pre_inst_state                   false
% 4.01/0.98  --bmc1_pre_inst_reach_state             false
% 4.01/0.98  --bmc1_out_unsat_core                   false
% 4.01/0.98  --bmc1_aig_witness_out                  false
% 4.01/0.98  --bmc1_verbose                          false
% 4.01/0.98  --bmc1_dump_clauses_tptp                false
% 4.01/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.01/0.98  --bmc1_dump_file                        -
% 4.01/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.01/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.01/0.98  --bmc1_ucm_extend_mode                  1
% 4.01/0.98  --bmc1_ucm_init_mode                    2
% 4.01/0.98  --bmc1_ucm_cone_mode                    none
% 4.01/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.01/0.98  --bmc1_ucm_relax_model                  4
% 4.01/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.01/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/0.98  --bmc1_ucm_layered_model                none
% 4.01/0.98  --bmc1_ucm_max_lemma_size               10
% 4.01/0.98  
% 4.01/0.98  ------ AIG Options
% 4.01/0.98  
% 4.01/0.98  --aig_mode                              false
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation Options
% 4.01/0.98  
% 4.01/0.98  --instantiation_flag                    true
% 4.01/0.98  --inst_sos_flag                         false
% 4.01/0.98  --inst_sos_phase                        true
% 4.01/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel_side                     num_symb
% 4.01/0.98  --inst_solver_per_active                1400
% 4.01/0.98  --inst_solver_calls_frac                1.
% 4.01/0.98  --inst_passive_queue_type               priority_queues
% 4.01/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/0.98  --inst_passive_queues_freq              [25;2]
% 4.01/0.98  --inst_dismatching                      true
% 4.01/0.98  --inst_eager_unprocessed_to_passive     true
% 4.01/0.98  --inst_prop_sim_given                   true
% 4.01/0.98  --inst_prop_sim_new                     false
% 4.01/0.98  --inst_subs_new                         false
% 4.01/0.98  --inst_eq_res_simp                      false
% 4.01/0.98  --inst_subs_given                       false
% 4.01/0.98  --inst_orphan_elimination               true
% 4.01/0.98  --inst_learning_loop_flag               true
% 4.01/0.98  --inst_learning_start                   3000
% 4.01/0.98  --inst_learning_factor                  2
% 4.01/0.98  --inst_start_prop_sim_after_learn       3
% 4.01/0.98  --inst_sel_renew                        solver
% 4.01/0.98  --inst_lit_activity_flag                true
% 4.01/0.98  --inst_restr_to_given                   false
% 4.01/0.98  --inst_activity_threshold               500
% 4.01/0.98  --inst_out_proof                        true
% 4.01/0.98  
% 4.01/0.98  ------ Resolution Options
% 4.01/0.98  
% 4.01/0.98  --resolution_flag                       true
% 4.01/0.98  --res_lit_sel                           adaptive
% 4.01/0.98  --res_lit_sel_side                      none
% 4.01/0.98  --res_ordering                          kbo
% 4.01/0.98  --res_to_prop_solver                    active
% 4.01/0.98  --res_prop_simpl_new                    false
% 4.01/0.98  --res_prop_simpl_given                  true
% 4.01/0.98  --res_passive_queue_type                priority_queues
% 4.01/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/0.98  --res_passive_queues_freq               [15;5]
% 4.01/0.98  --res_forward_subs                      full
% 4.01/0.98  --res_backward_subs                     full
% 4.01/0.98  --res_forward_subs_resolution           true
% 4.01/0.98  --res_backward_subs_resolution          true
% 4.01/0.98  --res_orphan_elimination                true
% 4.01/0.98  --res_time_limit                        2.
% 4.01/0.98  --res_out_proof                         true
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Options
% 4.01/0.98  
% 4.01/0.98  --superposition_flag                    true
% 4.01/0.98  --sup_passive_queue_type                priority_queues
% 4.01/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.01/0.98  --demod_completeness_check              fast
% 4.01/0.98  --demod_use_ground                      true
% 4.01/0.98  --sup_to_prop_solver                    passive
% 4.01/0.98  --sup_prop_simpl_new                    true
% 4.01/0.98  --sup_prop_simpl_given                  true
% 4.01/0.98  --sup_fun_splitting                     false
% 4.01/0.98  --sup_smt_interval                      50000
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Simplification Setup
% 4.01/0.98  
% 4.01/0.98  --sup_indices_passive                   []
% 4.01/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_full_bw                           [BwDemod]
% 4.01/0.98  --sup_immed_triv                        [TrivRules]
% 4.01/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_immed_bw_main                     []
% 4.01/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  
% 4.01/0.98  ------ Combination Options
% 4.01/0.98  
% 4.01/0.98  --comb_res_mult                         3
% 4.01/0.98  --comb_sup_mult                         2
% 4.01/0.98  --comb_inst_mult                        10
% 4.01/0.98  
% 4.01/0.98  ------ Debug Options
% 4.01/0.98  
% 4.01/0.98  --dbg_backtrace                         false
% 4.01/0.98  --dbg_dump_prop_clauses                 false
% 4.01/0.98  --dbg_dump_prop_clauses_file            -
% 4.01/0.98  --dbg_out_stat                          false
% 4.01/0.98  ------ Parsing...
% 4.01/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.01/0.98  ------ Proving...
% 4.01/0.98  ------ Problem Properties 
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  clauses                                 12
% 4.01/0.98  conjectures                             3
% 4.01/0.98  EPR                                     0
% 4.01/0.98  Horn                                    12
% 4.01/0.98  unary                                   3
% 4.01/0.98  binary                                  7
% 4.01/0.98  lits                                    23
% 4.01/0.98  lits eq                                 6
% 4.01/0.98  fd_pure                                 0
% 4.01/0.98  fd_pseudo                               0
% 4.01/0.98  fd_cond                                 0
% 4.01/0.98  fd_pseudo_cond                          0
% 4.01/0.98  AC symbols                              0
% 4.01/0.98  
% 4.01/0.98  ------ Schedule dynamic 5 is on 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  ------ 
% 4.01/0.98  Current options:
% 4.01/0.98  ------ 
% 4.01/0.98  
% 4.01/0.98  ------ Input Options
% 4.01/0.98  
% 4.01/0.98  --out_options                           all
% 4.01/0.98  --tptp_safe_out                         true
% 4.01/0.98  --problem_path                          ""
% 4.01/0.98  --include_path                          ""
% 4.01/0.98  --clausifier                            res/vclausify_rel
% 4.01/0.98  --clausifier_options                    --mode clausify
% 4.01/0.98  --stdin                                 false
% 4.01/0.98  --stats_out                             all
% 4.01/0.98  
% 4.01/0.98  ------ General Options
% 4.01/0.98  
% 4.01/0.98  --fof                                   false
% 4.01/0.98  --time_out_real                         305.
% 4.01/0.98  --time_out_virtual                      -1.
% 4.01/0.98  --symbol_type_check                     false
% 4.01/0.98  --clausify_out                          false
% 4.01/0.98  --sig_cnt_out                           false
% 4.01/0.98  --trig_cnt_out                          false
% 4.01/0.98  --trig_cnt_out_tolerance                1.
% 4.01/0.98  --trig_cnt_out_sk_spl                   false
% 4.01/0.98  --abstr_cl_out                          false
% 4.01/0.98  
% 4.01/0.98  ------ Global Options
% 4.01/0.98  
% 4.01/0.98  --schedule                              default
% 4.01/0.98  --add_important_lit                     false
% 4.01/0.98  --prop_solver_per_cl                    1000
% 4.01/0.98  --min_unsat_core                        false
% 4.01/0.98  --soft_assumptions                      false
% 4.01/0.98  --soft_lemma_size                       3
% 4.01/0.98  --prop_impl_unit_size                   0
% 4.01/0.98  --prop_impl_unit                        []
% 4.01/0.98  --share_sel_clauses                     true
% 4.01/0.98  --reset_solvers                         false
% 4.01/0.98  --bc_imp_inh                            [conj_cone]
% 4.01/0.98  --conj_cone_tolerance                   3.
% 4.01/0.98  --extra_neg_conj                        none
% 4.01/0.98  --large_theory_mode                     true
% 4.01/0.98  --prolific_symb_bound                   200
% 4.01/0.98  --lt_threshold                          2000
% 4.01/0.98  --clause_weak_htbl                      true
% 4.01/0.98  --gc_record_bc_elim                     false
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing Options
% 4.01/0.98  
% 4.01/0.98  --preprocessing_flag                    true
% 4.01/0.98  --time_out_prep_mult                    0.1
% 4.01/0.98  --splitting_mode                        input
% 4.01/0.98  --splitting_grd                         true
% 4.01/0.98  --splitting_cvd                         false
% 4.01/0.98  --splitting_cvd_svl                     false
% 4.01/0.98  --splitting_nvd                         32
% 4.01/0.98  --sub_typing                            true
% 4.01/0.98  --prep_gs_sim                           true
% 4.01/0.98  --prep_unflatten                        true
% 4.01/0.98  --prep_res_sim                          true
% 4.01/0.98  --prep_upred                            true
% 4.01/0.98  --prep_sem_filter                       exhaustive
% 4.01/0.98  --prep_sem_filter_out                   false
% 4.01/0.98  --pred_elim                             true
% 4.01/0.98  --res_sim_input                         true
% 4.01/0.98  --eq_ax_congr_red                       true
% 4.01/0.98  --pure_diseq_elim                       true
% 4.01/0.98  --brand_transform                       false
% 4.01/0.98  --non_eq_to_eq                          false
% 4.01/0.98  --prep_def_merge                        true
% 4.01/0.98  --prep_def_merge_prop_impl              false
% 4.01/0.98  --prep_def_merge_mbd                    true
% 4.01/0.98  --prep_def_merge_tr_red                 false
% 4.01/0.98  --prep_def_merge_tr_cl                  false
% 4.01/0.98  --smt_preprocessing                     true
% 4.01/0.98  --smt_ac_axioms                         fast
% 4.01/0.98  --preprocessed_out                      false
% 4.01/0.98  --preprocessed_stats                    false
% 4.01/0.98  
% 4.01/0.98  ------ Abstraction refinement Options
% 4.01/0.98  
% 4.01/0.98  --abstr_ref                             []
% 4.01/0.98  --abstr_ref_prep                        false
% 4.01/0.98  --abstr_ref_until_sat                   false
% 4.01/0.98  --abstr_ref_sig_restrict                funpre
% 4.01/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.01/0.98  --abstr_ref_under                       []
% 4.01/0.98  
% 4.01/0.98  ------ SAT Options
% 4.01/0.98  
% 4.01/0.98  --sat_mode                              false
% 4.01/0.98  --sat_fm_restart_options                ""
% 4.01/0.98  --sat_gr_def                            false
% 4.01/0.98  --sat_epr_types                         true
% 4.01/0.98  --sat_non_cyclic_types                  false
% 4.01/0.98  --sat_finite_models                     false
% 4.01/0.98  --sat_fm_lemmas                         false
% 4.01/0.98  --sat_fm_prep                           false
% 4.01/0.98  --sat_fm_uc_incr                        true
% 4.01/0.98  --sat_out_model                         small
% 4.01/0.98  --sat_out_clauses                       false
% 4.01/0.98  
% 4.01/0.98  ------ QBF Options
% 4.01/0.98  
% 4.01/0.98  --qbf_mode                              false
% 4.01/0.98  --qbf_elim_univ                         false
% 4.01/0.98  --qbf_dom_inst                          none
% 4.01/0.98  --qbf_dom_pre_inst                      false
% 4.01/0.98  --qbf_sk_in                             false
% 4.01/0.98  --qbf_pred_elim                         true
% 4.01/0.98  --qbf_split                             512
% 4.01/0.98  
% 4.01/0.98  ------ BMC1 Options
% 4.01/0.98  
% 4.01/0.98  --bmc1_incremental                      false
% 4.01/0.98  --bmc1_axioms                           reachable_all
% 4.01/0.98  --bmc1_min_bound                        0
% 4.01/0.98  --bmc1_max_bound                        -1
% 4.01/0.98  --bmc1_max_bound_default                -1
% 4.01/0.98  --bmc1_symbol_reachability              true
% 4.01/0.98  --bmc1_property_lemmas                  false
% 4.01/0.98  --bmc1_k_induction                      false
% 4.01/0.98  --bmc1_non_equiv_states                 false
% 4.01/0.98  --bmc1_deadlock                         false
% 4.01/0.98  --bmc1_ucm                              false
% 4.01/0.98  --bmc1_add_unsat_core                   none
% 4.01/0.98  --bmc1_unsat_core_children              false
% 4.01/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.01/0.98  --bmc1_out_stat                         full
% 4.01/0.98  --bmc1_ground_init                      false
% 4.01/0.98  --bmc1_pre_inst_next_state              false
% 4.01/0.98  --bmc1_pre_inst_state                   false
% 4.01/0.98  --bmc1_pre_inst_reach_state             false
% 4.01/0.98  --bmc1_out_unsat_core                   false
% 4.01/0.98  --bmc1_aig_witness_out                  false
% 4.01/0.98  --bmc1_verbose                          false
% 4.01/0.98  --bmc1_dump_clauses_tptp                false
% 4.01/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.01/0.98  --bmc1_dump_file                        -
% 4.01/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.01/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.01/0.98  --bmc1_ucm_extend_mode                  1
% 4.01/0.98  --bmc1_ucm_init_mode                    2
% 4.01/0.98  --bmc1_ucm_cone_mode                    none
% 4.01/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.01/0.98  --bmc1_ucm_relax_model                  4
% 4.01/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.01/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.01/0.98  --bmc1_ucm_layered_model                none
% 4.01/0.98  --bmc1_ucm_max_lemma_size               10
% 4.01/0.98  
% 4.01/0.98  ------ AIG Options
% 4.01/0.98  
% 4.01/0.98  --aig_mode                              false
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation Options
% 4.01/0.98  
% 4.01/0.98  --instantiation_flag                    true
% 4.01/0.98  --inst_sos_flag                         false
% 4.01/0.98  --inst_sos_phase                        true
% 4.01/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.01/0.98  --inst_lit_sel_side                     none
% 4.01/0.98  --inst_solver_per_active                1400
% 4.01/0.98  --inst_solver_calls_frac                1.
% 4.01/0.98  --inst_passive_queue_type               priority_queues
% 4.01/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.01/0.98  --inst_passive_queues_freq              [25;2]
% 4.01/0.98  --inst_dismatching                      true
% 4.01/0.98  --inst_eager_unprocessed_to_passive     true
% 4.01/0.98  --inst_prop_sim_given                   true
% 4.01/0.98  --inst_prop_sim_new                     false
% 4.01/0.98  --inst_subs_new                         false
% 4.01/0.98  --inst_eq_res_simp                      false
% 4.01/0.98  --inst_subs_given                       false
% 4.01/0.98  --inst_orphan_elimination               true
% 4.01/0.98  --inst_learning_loop_flag               true
% 4.01/0.98  --inst_learning_start                   3000
% 4.01/0.98  --inst_learning_factor                  2
% 4.01/0.98  --inst_start_prop_sim_after_learn       3
% 4.01/0.98  --inst_sel_renew                        solver
% 4.01/0.98  --inst_lit_activity_flag                true
% 4.01/0.98  --inst_restr_to_given                   false
% 4.01/0.98  --inst_activity_threshold               500
% 4.01/0.98  --inst_out_proof                        true
% 4.01/0.98  
% 4.01/0.98  ------ Resolution Options
% 4.01/0.98  
% 4.01/0.98  --resolution_flag                       false
% 4.01/0.98  --res_lit_sel                           adaptive
% 4.01/0.98  --res_lit_sel_side                      none
% 4.01/0.98  --res_ordering                          kbo
% 4.01/0.98  --res_to_prop_solver                    active
% 4.01/0.98  --res_prop_simpl_new                    false
% 4.01/0.98  --res_prop_simpl_given                  true
% 4.01/0.98  --res_passive_queue_type                priority_queues
% 4.01/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.01/0.98  --res_passive_queues_freq               [15;5]
% 4.01/0.98  --res_forward_subs                      full
% 4.01/0.98  --res_backward_subs                     full
% 4.01/0.98  --res_forward_subs_resolution           true
% 4.01/0.98  --res_backward_subs_resolution          true
% 4.01/0.98  --res_orphan_elimination                true
% 4.01/0.98  --res_time_limit                        2.
% 4.01/0.98  --res_out_proof                         true
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Options
% 4.01/0.98  
% 4.01/0.98  --superposition_flag                    true
% 4.01/0.98  --sup_passive_queue_type                priority_queues
% 4.01/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.01/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.01/0.98  --demod_completeness_check              fast
% 4.01/0.98  --demod_use_ground                      true
% 4.01/0.98  --sup_to_prop_solver                    passive
% 4.01/0.98  --sup_prop_simpl_new                    true
% 4.01/0.98  --sup_prop_simpl_given                  true
% 4.01/0.98  --sup_fun_splitting                     false
% 4.01/0.98  --sup_smt_interval                      50000
% 4.01/0.98  
% 4.01/0.98  ------ Superposition Simplification Setup
% 4.01/0.98  
% 4.01/0.98  --sup_indices_passive                   []
% 4.01/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.01/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.01/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_full_bw                           [BwDemod]
% 4.01/0.98  --sup_immed_triv                        [TrivRules]
% 4.01/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.01/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_immed_bw_main                     []
% 4.01/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.01/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.01/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.01/0.98  
% 4.01/0.98  ------ Combination Options
% 4.01/0.98  
% 4.01/0.98  --comb_res_mult                         3
% 4.01/0.98  --comb_sup_mult                         2
% 4.01/0.98  --comb_inst_mult                        10
% 4.01/0.98  
% 4.01/0.98  ------ Debug Options
% 4.01/0.98  
% 4.01/0.98  --dbg_backtrace                         false
% 4.01/0.98  --dbg_dump_prop_clauses                 false
% 4.01/0.98  --dbg_dump_prop_clauses_file            -
% 4.01/0.98  --dbg_out_stat                          false
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  ------ Proving...
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS status Theorem for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  fof(f11,conjecture,(
% 4.01/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f12,negated_conjecture,(
% 4.01/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))))))),
% 4.01/0.98    inference(negated_conjecture,[],[f11])).
% 4.01/0.98  
% 4.01/0.98  fof(f26,plain,(
% 4.01/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) & v3_pre_topc(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f12])).
% 4.01/0.98  
% 4.01/0.98  fof(f27,plain,(
% 4.01/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.01/0.98    inference(flattening,[],[f26])).
% 4.01/0.98  
% 4.01/0.98  fof(f31,plain,(
% 4.01/0.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2))) & v3_pre_topc(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f30,plain,(
% 4.01/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(X0),sK1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2))) & v3_pre_topc(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f29,plain,(
% 4.01/0.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2))) & v3_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.01/0.98    introduced(choice_axiom,[])).
% 4.01/0.98  
% 4.01/0.98  fof(f32,plain,(
% 4.01/0.98    ((~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.01/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31,f30,f29])).
% 4.01/0.98  
% 4.01/0.98  fof(f48,plain,(
% 4.01/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.01/0.98    inference(cnf_transformation,[],[f32])).
% 4.01/0.98  
% 4.01/0.98  fof(f1,axiom,(
% 4.01/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f13,plain,(
% 4.01/0.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f1])).
% 4.01/0.98  
% 4.01/0.98  fof(f33,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.01/0.98    inference(cnf_transformation,[],[f13])).
% 4.01/0.98  
% 4.01/0.98  fof(f47,plain,(
% 4.01/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.01/0.98    inference(cnf_transformation,[],[f32])).
% 4.01/0.98  
% 4.01/0.98  fof(f7,axiom,(
% 4.01/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f19,plain,(
% 4.01/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f7])).
% 4.01/0.98  
% 4.01/0.98  fof(f20,plain,(
% 4.01/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.01/0.98    inference(flattening,[],[f19])).
% 4.01/0.98  
% 4.01/0.98  fof(f39,plain,(
% 4.01/0.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f20])).
% 4.01/0.98  
% 4.01/0.98  fof(f46,plain,(
% 4.01/0.98    l1_pre_topc(sK0)),
% 4.01/0.98    inference(cnf_transformation,[],[f32])).
% 4.01/0.98  
% 4.01/0.98  fof(f3,axiom,(
% 4.01/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f15,plain,(
% 4.01/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f3])).
% 4.01/0.98  
% 4.01/0.98  fof(f35,plain,(
% 4.01/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.01/0.98    inference(cnf_transformation,[],[f15])).
% 4.01/0.98  
% 4.01/0.98  fof(f6,axiom,(
% 4.01/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f18,plain,(
% 4.01/0.98    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f6])).
% 4.01/0.98  
% 4.01/0.98  fof(f38,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.01/0.98    inference(cnf_transformation,[],[f18])).
% 4.01/0.98  
% 4.01/0.98  fof(f4,axiom,(
% 4.01/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f16,plain,(
% 4.01/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f4])).
% 4.01/0.98  
% 4.01/0.98  fof(f36,plain,(
% 4.01/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.01/0.98    inference(cnf_transformation,[],[f16])).
% 4.01/0.98  
% 4.01/0.98  fof(f8,axiom,(
% 4.01/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f21,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f8])).
% 4.01/0.98  
% 4.01/0.98  fof(f22,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.01/0.98    inference(flattening,[],[f21])).
% 4.01/0.98  
% 4.01/0.98  fof(f40,plain,(
% 4.01/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f22])).
% 4.01/0.98  
% 4.01/0.98  fof(f9,axiom,(
% 4.01/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f23,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.01/0.98    inference(ennf_transformation,[],[f9])).
% 4.01/0.98  
% 4.01/0.98  fof(f28,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.01/0.98    inference(nnf_transformation,[],[f23])).
% 4.01/0.98  
% 4.01/0.98  fof(f42,plain,(
% 4.01/0.98    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f28])).
% 4.01/0.98  
% 4.01/0.98  fof(f49,plain,(
% 4.01/0.98    v3_pre_topc(sK1,sK0)),
% 4.01/0.98    inference(cnf_transformation,[],[f32])).
% 4.01/0.98  
% 4.01/0.98  fof(f10,axiom,(
% 4.01/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 4.01/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.01/0.98  
% 4.01/0.98  fof(f24,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.01/0.98    inference(ennf_transformation,[],[f10])).
% 4.01/0.98  
% 4.01/0.98  fof(f25,plain,(
% 4.01/0.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.01/0.98    inference(flattening,[],[f24])).
% 4.01/0.98  
% 4.01/0.98  fof(f44,plain,(
% 4.01/0.98    ( ! [X2,X0,X1] : (r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.01/0.98    inference(cnf_transformation,[],[f25])).
% 4.01/0.98  
% 4.01/0.98  fof(f45,plain,(
% 4.01/0.98    v2_pre_topc(sK0)),
% 4.01/0.98    inference(cnf_transformation,[],[f32])).
% 4.01/0.98  
% 4.01/0.98  fof(f50,plain,(
% 4.01/0.98    ~r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 4.01/0.98    inference(cnf_transformation,[],[f32])).
% 4.01/0.98  
% 4.01/0.98  cnf(c_14,negated_conjecture,
% 4.01/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.01/0.98      inference(cnf_transformation,[],[f48]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_481,negated_conjecture,
% 4.01/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_741,plain,
% 4.01/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_0,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.01/0.98      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f33]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_488,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 4.01/0.98      | k9_subset_1(X1_44,X0_44,X2_44) = k9_subset_1(X1_44,X2_44,X0_44) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_734,plain,
% 4.01/0.98      ( k9_subset_1(X0_44,X1_44,X2_44) = k9_subset_1(X0_44,X2_44,X1_44)
% 4.01/0.98      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1129,plain,
% 4.01/0.98      ( k9_subset_1(u1_struct_0(sK0),X0_44,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0_44) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_741,c_734]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_15,negated_conjecture,
% 4.01/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.01/0.98      inference(cnf_transformation,[],[f47]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_480,negated_conjecture,
% 4.01/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_742,plain,
% 4.01/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1130,plain,
% 4.01/0.98      ( k9_subset_1(u1_struct_0(sK0),X0_44,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0_44) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_742,c_734]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_6,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.01/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.01/0.98      | ~ l1_pre_topc(X1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f39]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_16,negated_conjecture,
% 4.01/0.98      ( l1_pre_topc(sK0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f46]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_335,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.01/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.01/0.98      | sK0 != X1 ),
% 4.01/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_16]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_336,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.01/0.98      inference(unflattening,[status(thm)],[c_335]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_478,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | m1_subset_1(k2_pre_topc(sK0,X0_44),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_336]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_744,plain,
% 4.01/0.98      ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.01/0.98      | m1_subset_1(k2_pre_topc(sK0,X0_44),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_2,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.01/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 4.01/0.98      inference(cnf_transformation,[],[f35]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_486,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 4.01/0.98      | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_736,plain,
% 4.01/0.98      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_5,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.01/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.01/0.98      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f38]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_483,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 4.01/0.98      | ~ m1_subset_1(X2_44,k1_zfmisc_1(X1_44))
% 4.01/0.98      | k9_subset_1(X1_44,X2_44,k3_subset_1(X1_44,X0_44)) = k7_subset_1(X1_44,X2_44,X0_44) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_739,plain,
% 4.01/0.98      ( k9_subset_1(X0_44,X1_44,k3_subset_1(X0_44,X2_44)) = k7_subset_1(X0_44,X1_44,X2_44)
% 4.01/0.98      | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1631,plain,
% 4.01/0.98      ( k9_subset_1(X0_44,X1_44,k3_subset_1(X0_44,k3_subset_1(X0_44,X2_44))) = k7_subset_1(X0_44,X1_44,k3_subset_1(X0_44,X2_44))
% 4.01/0.98      | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top
% 4.01/0.98      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_736,c_739]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8810,plain,
% 4.01/0.98      ( k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = k7_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK1))
% 4.01/0.98      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_742,c_1631]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_3,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.01/0.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 4.01/0.98      inference(cnf_transformation,[],[f36]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_485,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 4.01/0.98      | k3_subset_1(X1_44,k3_subset_1(X1_44,X0_44)) = X0_44 ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_737,plain,
% 4.01/0.98      ( k3_subset_1(X0_44,k3_subset_1(X0_44,X1_44)) = X1_44
% 4.01/0.98      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1286,plain,
% 4.01/0.98      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_742,c_737]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8833,plain,
% 4.01/0.98      ( k7_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),X0_44,sK1)
% 4.01/0.98      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_8810,c_1286]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9341,plain,
% 4.01/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),sK1)
% 4.01/0.98      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_744,c_8833]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_12117,plain,
% 4.01/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_741,c_9341]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_8,plain,
% 4.01/0.98      ( ~ v4_pre_topc(X0,X1)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.01/0.98      | ~ l1_pre_topc(X1)
% 4.01/0.98      | k2_pre_topc(X1,X0) = X0 ),
% 4.01/0.98      inference(cnf_transformation,[],[f40]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_320,plain,
% 4.01/0.98      ( ~ v4_pre_topc(X0,X1)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.01/0.98      | k2_pre_topc(X1,X0) = X0
% 4.01/0.98      | sK0 != X1 ),
% 4.01/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_321,plain,
% 4.01/0.98      ( ~ v4_pre_topc(X0,sK0)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | k2_pre_topc(sK0,X0) = X0 ),
% 4.01/0.98      inference(unflattening,[status(thm)],[c_320]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_10,plain,
% 4.01/0.98      ( ~ v3_pre_topc(X0,X1)
% 4.01/0.98      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),X0),X1)
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.01/0.98      | ~ l1_pre_topc(X1) ),
% 4.01/0.98      inference(cnf_transformation,[],[f42]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_13,negated_conjecture,
% 4.01/0.98      ( v3_pre_topc(sK1,sK0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f49]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_307,plain,
% 4.01/0.98      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 4.01/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.01/0.98      | ~ l1_pre_topc(X0)
% 4.01/0.98      | sK1 != X1
% 4.01/0.98      | sK0 != X0 ),
% 4.01/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_308,plain,
% 4.01/0.98      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 4.01/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | ~ l1_pre_topc(sK0) ),
% 4.01/0.98      inference(unflattening,[status(thm)],[c_307]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_310,plain,
% 4.01/0.98      ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_308,c_16,c_15]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_355,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | k2_pre_topc(sK0,X0) = X0
% 4.01/0.98      | k3_subset_1(u1_struct_0(sK0),sK1) != X0
% 4.01/0.98      | sK0 != sK0 ),
% 4.01/0.98      inference(resolution_lifted,[status(thm)],[c_321,c_310]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_356,plain,
% 4.01/0.98      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 4.01/0.98      inference(unflattening,[status(thm)],[c_355]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_477,plain,
% 4.01/0.98      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_356]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_745,plain,
% 4.01/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1)
% 4.01/0.98      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_821,plain,
% 4.01/0.98      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.01/0.98      inference(instantiation,[status(thm)],[c_486]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_969,plain,
% 4.01/0.98      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),sK1) ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_745,c_15,c_477,c_821]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_11,plain,
% 4.01/0.98      ( r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
% 4.01/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.01/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 4.01/0.98      | ~ v2_pre_topc(X0)
% 4.01/0.98      | ~ l1_pre_topc(X0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f44]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_17,negated_conjecture,
% 4.01/0.98      ( v2_pre_topc(sK0) ),
% 4.01/0.98      inference(cnf_transformation,[],[f45]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_235,plain,
% 4.01/0.98      ( r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
% 4.01/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.01/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 4.01/0.98      | ~ l1_pre_topc(X0)
% 4.01/0.98      | sK0 != X0 ),
% 4.01/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_236,plain,
% 4.01/0.98      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0,X1)))
% 4.01/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | ~ l1_pre_topc(sK0) ),
% 4.01/0.98      inference(unflattening,[status(thm)],[c_235]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_240,plain,
% 4.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0,X1))) ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_236,c_16]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_241,plain,
% 4.01/0.98      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0,X1)))
% 4.01/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_240]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_479,plain,
% 4.01/0.98      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k2_pre_topc(sK0,X1_44)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0_44,X1_44)))
% 4.01/0.98      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.01/0.98      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.01/0.98      inference(subtyping,[status(esa)],[c_241]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_743,plain,
% 4.01/0.98      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k2_pre_topc(sK0,X1_44)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0_44,X1_44))) = iProver_top
% 4.01/0.98      | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.01/0.98      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_974,plain,
% 4.01/0.98      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top
% 4.01/0.98      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.01/0.98      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_969,c_743]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_20,plain,
% 4.01/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_822,plain,
% 4.01/0.98      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 4.01/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1083,plain,
% 4.01/0.98      ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.01/0.98      | r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_974,c_20,c_822]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_1084,plain,
% 4.01/0.98      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_44),k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top
% 4.01/0.98      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.01/0.98      inference(renaming,[status(thm)],[c_1083]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_12203,plain,
% 4.01/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top
% 4.01/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_12117,c_1084]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_9339,plain,
% 4.01/0.98      ( k7_subset_1(u1_struct_0(sK0),sK2,k3_subset_1(u1_struct_0(sK0),sK1)) = k9_subset_1(u1_struct_0(sK0),sK2,sK1) ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_741,c_8833]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_12209,plain,
% 4.01/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))) = iProver_top
% 4.01/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.01/0.98      inference(light_normalisation,[status(thm)],[c_12203,c_9339]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_21,plain,
% 4.01/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_12901,plain,
% 4.01/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))) = iProver_top ),
% 4.01/0.98      inference(global_propositional_subsumption,
% 4.01/0.98                [status(thm)],
% 4.01/0.98                [c_12209,c_21]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_12906,plain,
% 4.01/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))) = iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1130,c_12901]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_12918,plain,
% 4.01/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) = iProver_top ),
% 4.01/0.98      inference(superposition,[status(thm)],[c_1129,c_12906]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_12,negated_conjecture,
% 4.01/0.98      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 4.01/0.98      inference(cnf_transformation,[],[f50]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(c_23,plain,
% 4.01/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
% 4.01/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.01/0.98  
% 4.01/0.98  cnf(contradiction,plain,
% 4.01/0.98      ( $false ),
% 4.01/0.98      inference(minisat,[status(thm)],[c_12918,c_23]) ).
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/0.98  
% 4.01/0.98  ------                               Statistics
% 4.01/0.98  
% 4.01/0.98  ------ General
% 4.01/0.98  
% 4.01/0.98  abstr_ref_over_cycles:                  0
% 4.01/0.98  abstr_ref_under_cycles:                 0
% 4.01/0.98  gc_basic_clause_elim:                   0
% 4.01/0.98  forced_gc_time:                         0
% 4.01/0.98  parsing_time:                           0.009
% 4.01/0.98  unif_index_cands_time:                  0.
% 4.01/0.98  unif_index_add_time:                    0.
% 4.01/0.98  orderings_time:                         0.
% 4.01/0.98  out_proof_time:                         0.01
% 4.01/0.98  total_time:                             0.456
% 4.01/0.98  num_of_symbols:                         50
% 4.01/0.98  num_of_terms:                           18965
% 4.01/0.98  
% 4.01/0.98  ------ Preprocessing
% 4.01/0.98  
% 4.01/0.98  num_of_splits:                          0
% 4.01/0.98  num_of_split_atoms:                     0
% 4.01/0.98  num_of_reused_defs:                     0
% 4.01/0.98  num_eq_ax_congr_red:                    9
% 4.01/0.98  num_of_sem_filtered_clauses:            1
% 4.01/0.98  num_of_subtypes:                        3
% 4.01/0.98  monotx_restored_types:                  0
% 4.01/0.98  sat_num_of_epr_types:                   0
% 4.01/0.98  sat_num_of_non_cyclic_types:            0
% 4.01/0.98  sat_guarded_non_collapsed_types:        1
% 4.01/0.98  num_pure_diseq_elim:                    0
% 4.01/0.98  simp_replaced_by:                       0
% 4.01/0.98  res_preprocessed:                       75
% 4.01/0.98  prep_upred:                             0
% 4.01/0.98  prep_unflattend:                        7
% 4.01/0.98  smt_new_axioms:                         0
% 4.01/0.98  pred_elim_cands:                        2
% 4.01/0.98  pred_elim:                              4
% 4.01/0.98  pred_elim_cl:                           6
% 4.01/0.98  pred_elim_cycles:                       8
% 4.01/0.98  merged_defs:                            0
% 4.01/0.98  merged_defs_ncl:                        0
% 4.01/0.98  bin_hyper_res:                          0
% 4.01/0.98  prep_cycles:                            4
% 4.01/0.98  pred_elim_time:                         0.004
% 4.01/0.98  splitting_time:                         0.
% 4.01/0.98  sem_filter_time:                        0.
% 4.01/0.98  monotx_time:                            0.
% 4.01/0.98  subtype_inf_time:                       0.
% 4.01/0.98  
% 4.01/0.98  ------ Problem properties
% 4.01/0.98  
% 4.01/0.98  clauses:                                12
% 4.01/0.98  conjectures:                            3
% 4.01/0.98  epr:                                    0
% 4.01/0.98  horn:                                   12
% 4.01/0.98  ground:                                 4
% 4.01/0.98  unary:                                  3
% 4.01/0.98  binary:                                 7
% 4.01/0.98  lits:                                   23
% 4.01/0.98  lits_eq:                                6
% 4.01/0.98  fd_pure:                                0
% 4.01/0.98  fd_pseudo:                              0
% 4.01/0.98  fd_cond:                                0
% 4.01/0.98  fd_pseudo_cond:                         0
% 4.01/0.98  ac_symbols:                             0
% 4.01/0.98  
% 4.01/0.98  ------ Propositional Solver
% 4.01/0.98  
% 4.01/0.98  prop_solver_calls:                      30
% 4.01/0.98  prop_fast_solver_calls:                 659
% 4.01/0.98  smt_solver_calls:                       0
% 4.01/0.98  smt_fast_solver_calls:                  0
% 4.01/0.98  prop_num_of_clauses:                    5251
% 4.01/0.98  prop_preprocess_simplified:             10763
% 4.01/0.98  prop_fo_subsumed:                       17
% 4.01/0.98  prop_solver_time:                       0.
% 4.01/0.98  smt_solver_time:                        0.
% 4.01/0.98  smt_fast_solver_time:                   0.
% 4.01/0.98  prop_fast_solver_time:                  0.
% 4.01/0.98  prop_unsat_core_time:                   0.
% 4.01/0.98  
% 4.01/0.98  ------ QBF
% 4.01/0.98  
% 4.01/0.98  qbf_q_res:                              0
% 4.01/0.98  qbf_num_tautologies:                    0
% 4.01/0.98  qbf_prep_cycles:                        0
% 4.01/0.98  
% 4.01/0.98  ------ BMC1
% 4.01/0.98  
% 4.01/0.98  bmc1_current_bound:                     -1
% 4.01/0.98  bmc1_last_solved_bound:                 -1
% 4.01/0.98  bmc1_unsat_core_size:                   -1
% 4.01/0.98  bmc1_unsat_core_parents_size:           -1
% 4.01/0.98  bmc1_merge_next_fun:                    0
% 4.01/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.01/0.98  
% 4.01/0.98  ------ Instantiation
% 4.01/0.98  
% 4.01/0.98  inst_num_of_clauses:                    1893
% 4.01/0.98  inst_num_in_passive:                    895
% 4.01/0.98  inst_num_in_active:                     774
% 4.01/0.98  inst_num_in_unprocessed:                228
% 4.01/0.98  inst_num_of_loops:                      820
% 4.01/0.98  inst_num_of_learning_restarts:          0
% 4.01/0.98  inst_num_moves_active_passive:          41
% 4.01/0.98  inst_lit_activity:                      0
% 4.01/0.98  inst_lit_activity_moves:                0
% 4.01/0.98  inst_num_tautologies:                   0
% 4.01/0.98  inst_num_prop_implied:                  0
% 4.01/0.98  inst_num_existing_simplified:           0
% 4.01/0.98  inst_num_eq_res_simplified:             0
% 4.01/0.98  inst_num_child_elim:                    0
% 4.01/0.98  inst_num_of_dismatching_blockings:      1878
% 4.01/0.98  inst_num_of_non_proper_insts:           2473
% 4.01/0.98  inst_num_of_duplicates:                 0
% 4.01/0.98  inst_inst_num_from_inst_to_res:         0
% 4.01/0.98  inst_dismatching_checking_time:         0.
% 4.01/0.98  
% 4.01/0.98  ------ Resolution
% 4.01/0.98  
% 4.01/0.98  res_num_of_clauses:                     0
% 4.01/0.98  res_num_in_passive:                     0
% 4.01/0.98  res_num_in_active:                      0
% 4.01/0.98  res_num_of_loops:                       79
% 4.01/0.98  res_forward_subset_subsumed:            128
% 4.01/0.98  res_backward_subset_subsumed:           14
% 4.01/0.98  res_forward_subsumed:                   0
% 4.01/0.98  res_backward_subsumed:                  0
% 4.01/0.98  res_forward_subsumption_resolution:     0
% 4.01/0.98  res_backward_subsumption_resolution:    0
% 4.01/0.98  res_clause_to_clause_subsumption:       942
% 4.01/0.98  res_orphan_elimination:                 0
% 4.01/0.98  res_tautology_del:                      548
% 4.01/0.98  res_num_eq_res_simplified:              0
% 4.01/0.98  res_num_sel_changes:                    0
% 4.01/0.98  res_moves_from_active_to_pass:          0
% 4.01/0.98  
% 4.01/0.98  ------ Superposition
% 4.01/0.98  
% 4.01/0.98  sup_time_total:                         0.
% 4.01/0.98  sup_time_generating:                    0.
% 4.01/0.98  sup_time_sim_full:                      0.
% 4.01/0.98  sup_time_sim_immed:                     0.
% 4.01/0.98  
% 4.01/0.98  sup_num_of_clauses:                     307
% 4.01/0.98  sup_num_in_active:                      160
% 4.01/0.98  sup_num_in_passive:                     147
% 4.01/0.98  sup_num_of_loops:                       163
% 4.01/0.98  sup_fw_superposition:                   304
% 4.01/0.98  sup_bw_superposition:                   106
% 4.01/0.98  sup_immediate_simplified:               112
% 4.01/0.98  sup_given_eliminated:                   0
% 4.01/0.98  comparisons_done:                       0
% 4.01/0.98  comparisons_avoided:                    0
% 4.01/0.98  
% 4.01/0.98  ------ Simplifications
% 4.01/0.98  
% 4.01/0.98  
% 4.01/0.98  sim_fw_subset_subsumed:                 7
% 4.01/0.98  sim_bw_subset_subsumed:                 19
% 4.01/0.98  sim_fw_subsumed:                        0
% 4.01/0.98  sim_bw_subsumed:                        0
% 4.01/0.98  sim_fw_subsumption_res:                 0
% 4.01/0.98  sim_bw_subsumption_res:                 0
% 4.01/0.98  sim_tautology_del:                      5
% 4.01/0.98  sim_eq_tautology_del:                   33
% 4.01/0.98  sim_eq_res_simp:                        0
% 4.01/0.98  sim_fw_demodulated:                     49
% 4.01/0.98  sim_bw_demodulated:                     4
% 4.01/0.98  sim_light_normalised:                   71
% 4.01/0.98  sim_joinable_taut:                      0
% 4.01/0.98  sim_joinable_simp:                      0
% 4.01/0.98  sim_ac_normalised:                      0
% 4.01/0.98  sim_smt_subsumption:                    0
% 4.01/0.98  
%------------------------------------------------------------------------------
