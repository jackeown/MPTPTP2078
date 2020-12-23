%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:28 EST 2020

% Result     : Theorem 7.92s
% Output     : CNFRefutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :  147 (2533 expanded)
%              Number of clauses        :   85 ( 847 expanded)
%              Number of leaves         :   20 ( 584 expanded)
%              Depth                    :   21
%              Number of atoms          :  327 (7863 expanded)
%              Number of equality atoms :  109 (1338 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f31])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK2),X0)
          | ~ v4_pre_topc(sK2,X0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK2),X0)
          | v4_pre_topc(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X1),sK1)
            | ~ v4_pre_topc(X1,sK1) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X1),sK1)
            | v4_pre_topc(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
      | ~ v4_pre_topc(sK2,sK1) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
      | v4_pre_topc(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f37,f36])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f43,f41,f41])).

fof(f60,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_264,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_2,c_3])).

cnf(c_815,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_816,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_250,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_16,c_13])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_292,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_250,c_20])).

cnf(c_293,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_823,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_816,c_293])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_819,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_989,plain,
    ( r2_hidden(X0,k2_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_823,c_819])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_275,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_814,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_1197,plain,
    ( k3_xboole_0(X0,k2_struct_0(sK1)) = X0
    | r2_hidden(sK0(X0,k2_struct_0(sK1)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_814])).

cnf(c_3253,plain,
    ( k3_xboole_0(sK2,k2_struct_0(sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_815,c_1197])).

cnf(c_4,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_12,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1049,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_12])).

cnf(c_1104,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1049,c_12])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_822,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1436,plain,
    ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),sK2)) = k3_subset_1(k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_823,c_822])).

cnf(c_1592,plain,
    ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(sK2,k2_struct_0(sK1))) = k3_subset_1(k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_1104,c_1436])).

cnf(c_3264,plain,
    ( k3_subset_1(k2_struct_0(sK1),sK2) = k5_xboole_0(k2_struct_0(sK1),sK2) ),
    inference(demodulation,[status(thm)],[c_3253,c_1592])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_820,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3379,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3264,c_820])).

cnf(c_10842,plain,
    ( m1_subset_1(k5_xboole_0(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3379,c_823])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_818,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_10851,plain,
    ( k9_subset_1(k2_struct_0(sK1),X0,k5_xboole_0(k2_struct_0(sK1),sK2)) = k3_xboole_0(X0,k5_xboole_0(k2_struct_0(sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_10842,c_818])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_821,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_824,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_821,c_5])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_817,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2628,plain,
    ( k9_subset_1(X0,X0,k3_subset_1(X0,X1)) = k7_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_824,c_817])).

cnf(c_9625,plain,
    ( k9_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_823,c_2628])).

cnf(c_9631,plain,
    ( k9_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),k5_xboole_0(k2_struct_0(sK1),sK2)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(light_normalisation,[status(thm)],[c_9625,c_3264])).

cnf(c_10869,plain,
    ( k3_xboole_0(k2_struct_0(sK1),k5_xboole_0(k2_struct_0(sK1),sK2)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_10851,c_9631])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1595,plain,
    ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2))) = k3_xboole_0(k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_1436,c_0])).

cnf(c_1660,plain,
    ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),sK2))) = k3_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_1595,c_0])).

cnf(c_1704,plain,
    ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),k3_xboole_0(sK2,k2_struct_0(sK1)))) = k3_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_1104,c_1660])).

cnf(c_3260,plain,
    ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),sK2)) = k3_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2)) ),
    inference(demodulation,[status(thm)],[c_3253,c_1704])).

cnf(c_3269,plain,
    ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),sK2)) = k3_xboole_0(k2_struct_0(sK1),k5_xboole_0(k2_struct_0(sK1),sK2)) ),
    inference(demodulation,[status(thm)],[c_3260,c_3264])).

cnf(c_3270,plain,
    ( k3_xboole_0(k2_struct_0(sK1),k5_xboole_0(k2_struct_0(sK1),sK2)) = k3_subset_1(k2_struct_0(sK1),sK2) ),
    inference(light_normalisation,[status(thm)],[c_3269,c_1436])).

cnf(c_3326,plain,
    ( k3_xboole_0(k2_struct_0(sK1),k5_xboole_0(k2_struct_0(sK1),sK2)) = k5_xboole_0(k2_struct_0(sK1),sK2) ),
    inference(light_normalisation,[status(thm)],[c_3270,c_3264,c_3270])).

cnf(c_10870,plain,
    ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k5_xboole_0(k2_struct_0(sK1),sK2) ),
    inference(light_normalisation,[status(thm)],[c_10869,c_3326])).

cnf(c_17,negated_conjecture,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_144,plain,
    ( ~ v4_pre_topc(sK2,sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_145,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ v4_pre_topc(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_14,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_312,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_313,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
    | v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_352,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_145,c_313])).

cnf(c_353,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_412,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) ),
    inference(prop_impl,[status(thm)],[c_19,c_353])).

cnf(c_413,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(renaming,[status(thm)],[c_412])).

cnf(c_812,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_826,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_812,c_293])).

cnf(c_3373,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
    | v3_pre_topc(k5_xboole_0(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3264,c_826])).

cnf(c_15451,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10870,c_3373])).

cnf(c_18,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_146,plain,
    ( v4_pre_topc(sK2,sK1)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_147,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v4_pre_topc(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_146])).

cnf(c_15,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_297,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_298,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_338,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_147,c_298])).

cnf(c_339,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_414,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) ),
    inference(prop_impl,[status(thm)],[c_19,c_339])).

cnf(c_415,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(renaming,[status(thm)],[c_414])).

cnf(c_813,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_825,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
    | v3_pre_topc(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_813,c_293])).

cnf(c_3372,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
    | v3_pre_topc(k5_xboole_0(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3264,c_825])).

cnf(c_15450,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10870,c_3372])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15451,c_15450])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:04:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.92/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.92/1.49  
% 7.92/1.49  ------  iProver source info
% 7.92/1.49  
% 7.92/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.92/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.92/1.49  git: non_committed_changes: false
% 7.92/1.49  git: last_make_outside_of_git: false
% 7.92/1.49  
% 7.92/1.49  ------ 
% 7.92/1.49  
% 7.92/1.49  ------ Input Options
% 7.92/1.49  
% 7.92/1.49  --out_options                           all
% 7.92/1.49  --tptp_safe_out                         true
% 7.92/1.49  --problem_path                          ""
% 7.92/1.49  --include_path                          ""
% 7.92/1.49  --clausifier                            res/vclausify_rel
% 7.92/1.49  --clausifier_options                    ""
% 7.92/1.49  --stdin                                 false
% 7.92/1.49  --stats_out                             all
% 7.92/1.49  
% 7.92/1.49  ------ General Options
% 7.92/1.49  
% 7.92/1.49  --fof                                   false
% 7.92/1.49  --time_out_real                         305.
% 7.92/1.49  --time_out_virtual                      -1.
% 7.92/1.49  --symbol_type_check                     false
% 7.92/1.49  --clausify_out                          false
% 7.92/1.49  --sig_cnt_out                           false
% 7.92/1.49  --trig_cnt_out                          false
% 7.92/1.49  --trig_cnt_out_tolerance                1.
% 7.92/1.49  --trig_cnt_out_sk_spl                   false
% 7.92/1.49  --abstr_cl_out                          false
% 7.92/1.49  
% 7.92/1.49  ------ Global Options
% 7.92/1.49  
% 7.92/1.49  --schedule                              default
% 7.92/1.49  --add_important_lit                     false
% 7.92/1.49  --prop_solver_per_cl                    1000
% 7.92/1.49  --min_unsat_core                        false
% 7.92/1.49  --soft_assumptions                      false
% 7.92/1.49  --soft_lemma_size                       3
% 7.92/1.49  --prop_impl_unit_size                   0
% 7.92/1.49  --prop_impl_unit                        []
% 7.92/1.49  --share_sel_clauses                     true
% 7.92/1.49  --reset_solvers                         false
% 7.92/1.49  --bc_imp_inh                            [conj_cone]
% 7.92/1.49  --conj_cone_tolerance                   3.
% 7.92/1.49  --extra_neg_conj                        none
% 7.92/1.49  --large_theory_mode                     true
% 7.92/1.49  --prolific_symb_bound                   200
% 7.92/1.49  --lt_threshold                          2000
% 7.92/1.49  --clause_weak_htbl                      true
% 7.92/1.49  --gc_record_bc_elim                     false
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing Options
% 7.92/1.49  
% 7.92/1.49  --preprocessing_flag                    true
% 7.92/1.49  --time_out_prep_mult                    0.1
% 7.92/1.49  --splitting_mode                        input
% 7.92/1.49  --splitting_grd                         true
% 7.92/1.49  --splitting_cvd                         false
% 7.92/1.49  --splitting_cvd_svl                     false
% 7.92/1.49  --splitting_nvd                         32
% 7.92/1.49  --sub_typing                            true
% 7.92/1.49  --prep_gs_sim                           true
% 7.92/1.49  --prep_unflatten                        true
% 7.92/1.49  --prep_res_sim                          true
% 7.92/1.49  --prep_upred                            true
% 7.92/1.49  --prep_sem_filter                       exhaustive
% 7.92/1.49  --prep_sem_filter_out                   false
% 7.92/1.49  --pred_elim                             true
% 7.92/1.49  --res_sim_input                         true
% 7.92/1.49  --eq_ax_congr_red                       true
% 7.92/1.49  --pure_diseq_elim                       true
% 7.92/1.49  --brand_transform                       false
% 7.92/1.49  --non_eq_to_eq                          false
% 7.92/1.49  --prep_def_merge                        true
% 7.92/1.49  --prep_def_merge_prop_impl              false
% 7.92/1.49  --prep_def_merge_mbd                    true
% 7.92/1.49  --prep_def_merge_tr_red                 false
% 7.92/1.49  --prep_def_merge_tr_cl                  false
% 7.92/1.49  --smt_preprocessing                     true
% 7.92/1.49  --smt_ac_axioms                         fast
% 7.92/1.49  --preprocessed_out                      false
% 7.92/1.49  --preprocessed_stats                    false
% 7.92/1.49  
% 7.92/1.49  ------ Abstraction refinement Options
% 7.92/1.49  
% 7.92/1.49  --abstr_ref                             []
% 7.92/1.49  --abstr_ref_prep                        false
% 7.92/1.49  --abstr_ref_until_sat                   false
% 7.92/1.49  --abstr_ref_sig_restrict                funpre
% 7.92/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.92/1.49  --abstr_ref_under                       []
% 7.92/1.49  
% 7.92/1.49  ------ SAT Options
% 7.92/1.49  
% 7.92/1.49  --sat_mode                              false
% 7.92/1.49  --sat_fm_restart_options                ""
% 7.92/1.49  --sat_gr_def                            false
% 7.92/1.49  --sat_epr_types                         true
% 7.92/1.49  --sat_non_cyclic_types                  false
% 7.92/1.49  --sat_finite_models                     false
% 7.92/1.49  --sat_fm_lemmas                         false
% 7.92/1.49  --sat_fm_prep                           false
% 7.92/1.49  --sat_fm_uc_incr                        true
% 7.92/1.49  --sat_out_model                         small
% 7.92/1.49  --sat_out_clauses                       false
% 7.92/1.49  
% 7.92/1.49  ------ QBF Options
% 7.92/1.49  
% 7.92/1.49  --qbf_mode                              false
% 7.92/1.49  --qbf_elim_univ                         false
% 7.92/1.49  --qbf_dom_inst                          none
% 7.92/1.49  --qbf_dom_pre_inst                      false
% 7.92/1.49  --qbf_sk_in                             false
% 7.92/1.49  --qbf_pred_elim                         true
% 7.92/1.49  --qbf_split                             512
% 7.92/1.49  
% 7.92/1.49  ------ BMC1 Options
% 7.92/1.49  
% 7.92/1.49  --bmc1_incremental                      false
% 7.92/1.49  --bmc1_axioms                           reachable_all
% 7.92/1.49  --bmc1_min_bound                        0
% 7.92/1.49  --bmc1_max_bound                        -1
% 7.92/1.49  --bmc1_max_bound_default                -1
% 7.92/1.49  --bmc1_symbol_reachability              true
% 7.92/1.49  --bmc1_property_lemmas                  false
% 7.92/1.49  --bmc1_k_induction                      false
% 7.92/1.49  --bmc1_non_equiv_states                 false
% 7.92/1.49  --bmc1_deadlock                         false
% 7.92/1.49  --bmc1_ucm                              false
% 7.92/1.49  --bmc1_add_unsat_core                   none
% 7.92/1.49  --bmc1_unsat_core_children              false
% 7.92/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.92/1.49  --bmc1_out_stat                         full
% 7.92/1.49  --bmc1_ground_init                      false
% 7.92/1.49  --bmc1_pre_inst_next_state              false
% 7.92/1.49  --bmc1_pre_inst_state                   false
% 7.92/1.49  --bmc1_pre_inst_reach_state             false
% 7.92/1.49  --bmc1_out_unsat_core                   false
% 7.92/1.49  --bmc1_aig_witness_out                  false
% 7.92/1.49  --bmc1_verbose                          false
% 7.92/1.49  --bmc1_dump_clauses_tptp                false
% 7.92/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.92/1.49  --bmc1_dump_file                        -
% 7.92/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.92/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.92/1.49  --bmc1_ucm_extend_mode                  1
% 7.92/1.49  --bmc1_ucm_init_mode                    2
% 7.92/1.49  --bmc1_ucm_cone_mode                    none
% 7.92/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.92/1.49  --bmc1_ucm_relax_model                  4
% 7.92/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.92/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.92/1.49  --bmc1_ucm_layered_model                none
% 7.92/1.49  --bmc1_ucm_max_lemma_size               10
% 7.92/1.49  
% 7.92/1.49  ------ AIG Options
% 7.92/1.49  
% 7.92/1.49  --aig_mode                              false
% 7.92/1.49  
% 7.92/1.49  ------ Instantiation Options
% 7.92/1.49  
% 7.92/1.49  --instantiation_flag                    true
% 7.92/1.49  --inst_sos_flag                         true
% 7.92/1.49  --inst_sos_phase                        true
% 7.92/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.92/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.92/1.49  --inst_lit_sel_side                     num_symb
% 7.92/1.49  --inst_solver_per_active                1400
% 7.92/1.49  --inst_solver_calls_frac                1.
% 7.92/1.49  --inst_passive_queue_type               priority_queues
% 7.92/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.92/1.49  --inst_passive_queues_freq              [25;2]
% 7.92/1.49  --inst_dismatching                      true
% 7.92/1.49  --inst_eager_unprocessed_to_passive     true
% 7.92/1.49  --inst_prop_sim_given                   true
% 7.92/1.49  --inst_prop_sim_new                     false
% 7.92/1.49  --inst_subs_new                         false
% 7.92/1.49  --inst_eq_res_simp                      false
% 7.92/1.49  --inst_subs_given                       false
% 7.92/1.49  --inst_orphan_elimination               true
% 7.92/1.49  --inst_learning_loop_flag               true
% 7.92/1.49  --inst_learning_start                   3000
% 7.92/1.49  --inst_learning_factor                  2
% 7.92/1.49  --inst_start_prop_sim_after_learn       3
% 7.92/1.49  --inst_sel_renew                        solver
% 7.92/1.49  --inst_lit_activity_flag                true
% 7.92/1.49  --inst_restr_to_given                   false
% 7.92/1.49  --inst_activity_threshold               500
% 7.92/1.49  --inst_out_proof                        true
% 7.92/1.49  
% 7.92/1.49  ------ Resolution Options
% 7.92/1.49  
% 7.92/1.49  --resolution_flag                       true
% 7.92/1.49  --res_lit_sel                           adaptive
% 7.92/1.49  --res_lit_sel_side                      none
% 7.92/1.49  --res_ordering                          kbo
% 7.92/1.49  --res_to_prop_solver                    active
% 7.92/1.49  --res_prop_simpl_new                    false
% 7.92/1.49  --res_prop_simpl_given                  true
% 7.92/1.49  --res_passive_queue_type                priority_queues
% 7.92/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.92/1.49  --res_passive_queues_freq               [15;5]
% 7.92/1.49  --res_forward_subs                      full
% 7.92/1.49  --res_backward_subs                     full
% 7.92/1.49  --res_forward_subs_resolution           true
% 7.92/1.49  --res_backward_subs_resolution          true
% 7.92/1.49  --res_orphan_elimination                true
% 7.92/1.49  --res_time_limit                        2.
% 7.92/1.49  --res_out_proof                         true
% 7.92/1.49  
% 7.92/1.49  ------ Superposition Options
% 7.92/1.49  
% 7.92/1.49  --superposition_flag                    true
% 7.92/1.49  --sup_passive_queue_type                priority_queues
% 7.92/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.92/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.92/1.49  --demod_completeness_check              fast
% 7.92/1.49  --demod_use_ground                      true
% 7.92/1.49  --sup_to_prop_solver                    passive
% 7.92/1.49  --sup_prop_simpl_new                    true
% 7.92/1.49  --sup_prop_simpl_given                  true
% 7.92/1.49  --sup_fun_splitting                     true
% 7.92/1.49  --sup_smt_interval                      50000
% 7.92/1.49  
% 7.92/1.49  ------ Superposition Simplification Setup
% 7.92/1.49  
% 7.92/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.92/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.92/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.92/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.92/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.92/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.92/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.92/1.49  --sup_immed_triv                        [TrivRules]
% 7.92/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_immed_bw_main                     []
% 7.92/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.92/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.92/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_input_bw                          []
% 7.92/1.49  
% 7.92/1.49  ------ Combination Options
% 7.92/1.49  
% 7.92/1.49  --comb_res_mult                         3
% 7.92/1.49  --comb_sup_mult                         2
% 7.92/1.49  --comb_inst_mult                        10
% 7.92/1.49  
% 7.92/1.49  ------ Debug Options
% 7.92/1.49  
% 7.92/1.49  --dbg_backtrace                         false
% 7.92/1.49  --dbg_dump_prop_clauses                 false
% 7.92/1.49  --dbg_dump_prop_clauses_file            -
% 7.92/1.49  --dbg_out_stat                          false
% 7.92/1.49  ------ Parsing...
% 7.92/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.92/1.49  ------ Proving...
% 7.92/1.49  ------ Problem Properties 
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  clauses                                 16
% 7.92/1.49  conjectures                             1
% 7.92/1.49  EPR                                     0
% 7.92/1.49  Horn                                    14
% 7.92/1.49  unary                                   7
% 7.92/1.49  binary                                  7
% 7.92/1.49  lits                                    27
% 7.92/1.49  lits eq                                 10
% 7.92/1.49  fd_pure                                 0
% 7.92/1.49  fd_pseudo                               0
% 7.92/1.49  fd_cond                                 0
% 7.92/1.49  fd_pseudo_cond                          0
% 7.92/1.49  AC symbols                              0
% 7.92/1.49  
% 7.92/1.49  ------ Schedule dynamic 5 is on 
% 7.92/1.49  
% 7.92/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  ------ 
% 7.92/1.49  Current options:
% 7.92/1.49  ------ 
% 7.92/1.49  
% 7.92/1.49  ------ Input Options
% 7.92/1.49  
% 7.92/1.49  --out_options                           all
% 7.92/1.49  --tptp_safe_out                         true
% 7.92/1.49  --problem_path                          ""
% 7.92/1.49  --include_path                          ""
% 7.92/1.49  --clausifier                            res/vclausify_rel
% 7.92/1.49  --clausifier_options                    ""
% 7.92/1.49  --stdin                                 false
% 7.92/1.49  --stats_out                             all
% 7.92/1.49  
% 7.92/1.49  ------ General Options
% 7.92/1.49  
% 7.92/1.49  --fof                                   false
% 7.92/1.49  --time_out_real                         305.
% 7.92/1.49  --time_out_virtual                      -1.
% 7.92/1.49  --symbol_type_check                     false
% 7.92/1.49  --clausify_out                          false
% 7.92/1.49  --sig_cnt_out                           false
% 7.92/1.49  --trig_cnt_out                          false
% 7.92/1.49  --trig_cnt_out_tolerance                1.
% 7.92/1.49  --trig_cnt_out_sk_spl                   false
% 7.92/1.49  --abstr_cl_out                          false
% 7.92/1.49  
% 7.92/1.49  ------ Global Options
% 7.92/1.49  
% 7.92/1.49  --schedule                              default
% 7.92/1.49  --add_important_lit                     false
% 7.92/1.49  --prop_solver_per_cl                    1000
% 7.92/1.49  --min_unsat_core                        false
% 7.92/1.49  --soft_assumptions                      false
% 7.92/1.49  --soft_lemma_size                       3
% 7.92/1.49  --prop_impl_unit_size                   0
% 7.92/1.49  --prop_impl_unit                        []
% 7.92/1.49  --share_sel_clauses                     true
% 7.92/1.49  --reset_solvers                         false
% 7.92/1.49  --bc_imp_inh                            [conj_cone]
% 7.92/1.49  --conj_cone_tolerance                   3.
% 7.92/1.49  --extra_neg_conj                        none
% 7.92/1.49  --large_theory_mode                     true
% 7.92/1.49  --prolific_symb_bound                   200
% 7.92/1.49  --lt_threshold                          2000
% 7.92/1.49  --clause_weak_htbl                      true
% 7.92/1.49  --gc_record_bc_elim                     false
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing Options
% 7.92/1.49  
% 7.92/1.49  --preprocessing_flag                    true
% 7.92/1.49  --time_out_prep_mult                    0.1
% 7.92/1.49  --splitting_mode                        input
% 7.92/1.49  --splitting_grd                         true
% 7.92/1.49  --splitting_cvd                         false
% 7.92/1.49  --splitting_cvd_svl                     false
% 7.92/1.49  --splitting_nvd                         32
% 7.92/1.49  --sub_typing                            true
% 7.92/1.49  --prep_gs_sim                           true
% 7.92/1.49  --prep_unflatten                        true
% 7.92/1.49  --prep_res_sim                          true
% 7.92/1.49  --prep_upred                            true
% 7.92/1.49  --prep_sem_filter                       exhaustive
% 7.92/1.49  --prep_sem_filter_out                   false
% 7.92/1.49  --pred_elim                             true
% 7.92/1.49  --res_sim_input                         true
% 7.92/1.49  --eq_ax_congr_red                       true
% 7.92/1.49  --pure_diseq_elim                       true
% 7.92/1.49  --brand_transform                       false
% 7.92/1.49  --non_eq_to_eq                          false
% 7.92/1.49  --prep_def_merge                        true
% 7.92/1.49  --prep_def_merge_prop_impl              false
% 7.92/1.49  --prep_def_merge_mbd                    true
% 7.92/1.49  --prep_def_merge_tr_red                 false
% 7.92/1.49  --prep_def_merge_tr_cl                  false
% 7.92/1.49  --smt_preprocessing                     true
% 7.92/1.49  --smt_ac_axioms                         fast
% 7.92/1.49  --preprocessed_out                      false
% 7.92/1.49  --preprocessed_stats                    false
% 7.92/1.49  
% 7.92/1.49  ------ Abstraction refinement Options
% 7.92/1.49  
% 7.92/1.49  --abstr_ref                             []
% 7.92/1.49  --abstr_ref_prep                        false
% 7.92/1.49  --abstr_ref_until_sat                   false
% 7.92/1.49  --abstr_ref_sig_restrict                funpre
% 7.92/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.92/1.49  --abstr_ref_under                       []
% 7.92/1.49  
% 7.92/1.49  ------ SAT Options
% 7.92/1.49  
% 7.92/1.49  --sat_mode                              false
% 7.92/1.49  --sat_fm_restart_options                ""
% 7.92/1.49  --sat_gr_def                            false
% 7.92/1.49  --sat_epr_types                         true
% 7.92/1.49  --sat_non_cyclic_types                  false
% 7.92/1.49  --sat_finite_models                     false
% 7.92/1.49  --sat_fm_lemmas                         false
% 7.92/1.49  --sat_fm_prep                           false
% 7.92/1.49  --sat_fm_uc_incr                        true
% 7.92/1.49  --sat_out_model                         small
% 7.92/1.49  --sat_out_clauses                       false
% 7.92/1.49  
% 7.92/1.49  ------ QBF Options
% 7.92/1.49  
% 7.92/1.49  --qbf_mode                              false
% 7.92/1.49  --qbf_elim_univ                         false
% 7.92/1.49  --qbf_dom_inst                          none
% 7.92/1.49  --qbf_dom_pre_inst                      false
% 7.92/1.49  --qbf_sk_in                             false
% 7.92/1.49  --qbf_pred_elim                         true
% 7.92/1.49  --qbf_split                             512
% 7.92/1.49  
% 7.92/1.49  ------ BMC1 Options
% 7.92/1.49  
% 7.92/1.49  --bmc1_incremental                      false
% 7.92/1.49  --bmc1_axioms                           reachable_all
% 7.92/1.49  --bmc1_min_bound                        0
% 7.92/1.49  --bmc1_max_bound                        -1
% 7.92/1.49  --bmc1_max_bound_default                -1
% 7.92/1.49  --bmc1_symbol_reachability              true
% 7.92/1.49  --bmc1_property_lemmas                  false
% 7.92/1.49  --bmc1_k_induction                      false
% 7.92/1.49  --bmc1_non_equiv_states                 false
% 7.92/1.49  --bmc1_deadlock                         false
% 7.92/1.49  --bmc1_ucm                              false
% 7.92/1.49  --bmc1_add_unsat_core                   none
% 7.92/1.49  --bmc1_unsat_core_children              false
% 7.92/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.92/1.49  --bmc1_out_stat                         full
% 7.92/1.49  --bmc1_ground_init                      false
% 7.92/1.49  --bmc1_pre_inst_next_state              false
% 7.92/1.49  --bmc1_pre_inst_state                   false
% 7.92/1.49  --bmc1_pre_inst_reach_state             false
% 7.92/1.49  --bmc1_out_unsat_core                   false
% 7.92/1.49  --bmc1_aig_witness_out                  false
% 7.92/1.49  --bmc1_verbose                          false
% 7.92/1.49  --bmc1_dump_clauses_tptp                false
% 7.92/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.92/1.49  --bmc1_dump_file                        -
% 7.92/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.92/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.92/1.49  --bmc1_ucm_extend_mode                  1
% 7.92/1.49  --bmc1_ucm_init_mode                    2
% 7.92/1.49  --bmc1_ucm_cone_mode                    none
% 7.92/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.92/1.49  --bmc1_ucm_relax_model                  4
% 7.92/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.92/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.92/1.49  --bmc1_ucm_layered_model                none
% 7.92/1.49  --bmc1_ucm_max_lemma_size               10
% 7.92/1.49  
% 7.92/1.49  ------ AIG Options
% 7.92/1.49  
% 7.92/1.49  --aig_mode                              false
% 7.92/1.49  
% 7.92/1.49  ------ Instantiation Options
% 7.92/1.49  
% 7.92/1.49  --instantiation_flag                    true
% 7.92/1.49  --inst_sos_flag                         true
% 7.92/1.49  --inst_sos_phase                        true
% 7.92/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.92/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.92/1.49  --inst_lit_sel_side                     none
% 7.92/1.49  --inst_solver_per_active                1400
% 7.92/1.49  --inst_solver_calls_frac                1.
% 7.92/1.49  --inst_passive_queue_type               priority_queues
% 7.92/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.92/1.49  --inst_passive_queues_freq              [25;2]
% 7.92/1.49  --inst_dismatching                      true
% 7.92/1.49  --inst_eager_unprocessed_to_passive     true
% 7.92/1.49  --inst_prop_sim_given                   true
% 7.92/1.49  --inst_prop_sim_new                     false
% 7.92/1.49  --inst_subs_new                         false
% 7.92/1.49  --inst_eq_res_simp                      false
% 7.92/1.49  --inst_subs_given                       false
% 7.92/1.49  --inst_orphan_elimination               true
% 7.92/1.49  --inst_learning_loop_flag               true
% 7.92/1.49  --inst_learning_start                   3000
% 7.92/1.49  --inst_learning_factor                  2
% 7.92/1.49  --inst_start_prop_sim_after_learn       3
% 7.92/1.49  --inst_sel_renew                        solver
% 7.92/1.49  --inst_lit_activity_flag                true
% 7.92/1.49  --inst_restr_to_given                   false
% 7.92/1.49  --inst_activity_threshold               500
% 7.92/1.49  --inst_out_proof                        true
% 7.92/1.49  
% 7.92/1.49  ------ Resolution Options
% 7.92/1.49  
% 7.92/1.49  --resolution_flag                       false
% 7.92/1.49  --res_lit_sel                           adaptive
% 7.92/1.49  --res_lit_sel_side                      none
% 7.92/1.49  --res_ordering                          kbo
% 7.92/1.49  --res_to_prop_solver                    active
% 7.92/1.49  --res_prop_simpl_new                    false
% 7.92/1.49  --res_prop_simpl_given                  true
% 7.92/1.49  --res_passive_queue_type                priority_queues
% 7.92/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.92/1.49  --res_passive_queues_freq               [15;5]
% 7.92/1.49  --res_forward_subs                      full
% 7.92/1.49  --res_backward_subs                     full
% 7.92/1.49  --res_forward_subs_resolution           true
% 7.92/1.49  --res_backward_subs_resolution          true
% 7.92/1.49  --res_orphan_elimination                true
% 7.92/1.49  --res_time_limit                        2.
% 7.92/1.49  --res_out_proof                         true
% 7.92/1.49  
% 7.92/1.49  ------ Superposition Options
% 7.92/1.49  
% 7.92/1.49  --superposition_flag                    true
% 7.92/1.49  --sup_passive_queue_type                priority_queues
% 7.92/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.92/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.92/1.49  --demod_completeness_check              fast
% 7.92/1.49  --demod_use_ground                      true
% 7.92/1.49  --sup_to_prop_solver                    passive
% 7.92/1.49  --sup_prop_simpl_new                    true
% 7.92/1.49  --sup_prop_simpl_given                  true
% 7.92/1.49  --sup_fun_splitting                     true
% 7.92/1.49  --sup_smt_interval                      50000
% 7.92/1.49  
% 7.92/1.49  ------ Superposition Simplification Setup
% 7.92/1.49  
% 7.92/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.92/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.92/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.92/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.92/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.92/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.92/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.92/1.49  --sup_immed_triv                        [TrivRules]
% 7.92/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_immed_bw_main                     []
% 7.92/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.92/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.92/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.92/1.49  --sup_input_bw                          []
% 7.92/1.49  
% 7.92/1.49  ------ Combination Options
% 7.92/1.49  
% 7.92/1.49  --comb_res_mult                         3
% 7.92/1.49  --comb_sup_mult                         2
% 7.92/1.49  --comb_inst_mult                        10
% 7.92/1.49  
% 7.92/1.49  ------ Debug Options
% 7.92/1.49  
% 7.92/1.49  --dbg_backtrace                         false
% 7.92/1.49  --dbg_dump_prop_clauses                 false
% 7.92/1.49  --dbg_dump_prop_clauses_file            -
% 7.92/1.49  --dbg_out_stat                          false
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  ------ Proving...
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  % SZS status Theorem for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  fof(f1,axiom,(
% 7.92/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f19,plain,(
% 7.92/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 7.92/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 7.92/1.49  
% 7.92/1.49  fof(f20,plain,(
% 7.92/1.49    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 7.92/1.49    inference(ennf_transformation,[],[f19])).
% 7.92/1.49  
% 7.92/1.49  fof(f31,plain,(
% 7.92/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f32,plain,(
% 7.92/1.49    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.92/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f31])).
% 7.92/1.49  
% 7.92/1.49  fof(f39,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f32])).
% 7.92/1.49  
% 7.92/1.49  fof(f3,axiom,(
% 7.92/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f21,plain,(
% 7.92/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.92/1.49    inference(ennf_transformation,[],[f3])).
% 7.92/1.49  
% 7.92/1.49  fof(f42,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f21])).
% 7.92/1.49  
% 7.92/1.49  fof(f17,conjecture,(
% 7.92/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f18,negated_conjecture,(
% 7.92/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.92/1.49    inference(negated_conjecture,[],[f17])).
% 7.92/1.49  
% 7.92/1.49  fof(f30,plain,(
% 7.92/1.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f18])).
% 7.92/1.49  
% 7.92/1.49  fof(f34,plain,(
% 7.92/1.49    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.92/1.49    inference(nnf_transformation,[],[f30])).
% 7.92/1.49  
% 7.92/1.49  fof(f35,plain,(
% 7.92/1.49    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.92/1.49    inference(flattening,[],[f34])).
% 7.92/1.49  
% 7.92/1.49  fof(f37,plain,(
% 7.92/1.49    ( ! [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK2),X0) | ~v4_pre_topc(sK2,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK2),X0) | v4_pre_topc(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f36,plain,(
% 7.92/1.49    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X1),sK1) | ~v4_pre_topc(X1,sK1)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK1),X1),sK1) | v4_pre_topc(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 7.92/1.49    introduced(choice_axiom,[])).
% 7.92/1.49  
% 7.92/1.49  fof(f38,plain,(
% 7.92/1.49    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) | ~v4_pre_topc(sK2,sK1)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) | v4_pre_topc(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 7.92/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f37,f36])).
% 7.92/1.49  
% 7.92/1.49  fof(f58,plain,(
% 7.92/1.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.92/1.49    inference(cnf_transformation,[],[f38])).
% 7.92/1.49  
% 7.92/1.49  fof(f16,axiom,(
% 7.92/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f29,plain,(
% 7.92/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f16])).
% 7.92/1.49  
% 7.92/1.49  fof(f56,plain,(
% 7.92/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f29])).
% 7.92/1.49  
% 7.92/1.49  fof(f14,axiom,(
% 7.92/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f27,plain,(
% 7.92/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f14])).
% 7.92/1.49  
% 7.92/1.49  fof(f53,plain,(
% 7.92/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f27])).
% 7.92/1.49  
% 7.92/1.49  fof(f57,plain,(
% 7.92/1.49    l1_pre_topc(sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f38])).
% 7.92/1.49  
% 7.92/1.49  fof(f10,axiom,(
% 7.92/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f24,plain,(
% 7.92/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.92/1.49    inference(ennf_transformation,[],[f10])).
% 7.92/1.49  
% 7.92/1.49  fof(f49,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f24])).
% 7.92/1.49  
% 7.92/1.49  fof(f40,plain,(
% 7.92/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f32])).
% 7.92/1.49  
% 7.92/1.49  fof(f5,axiom,(
% 7.92/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f44,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f5])).
% 7.92/1.49  
% 7.92/1.49  fof(f13,axiom,(
% 7.92/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f52,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f13])).
% 7.92/1.49  
% 7.92/1.49  fof(f7,axiom,(
% 7.92/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f22,plain,(
% 7.92/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.92/1.49    inference(ennf_transformation,[],[f7])).
% 7.92/1.49  
% 7.92/1.49  fof(f46,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f22])).
% 7.92/1.49  
% 7.92/1.49  fof(f2,axiom,(
% 7.92/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f41,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f2])).
% 7.92/1.49  
% 7.92/1.49  fof(f62,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.92/1.49    inference(definition_unfolding,[],[f46,f41])).
% 7.92/1.49  
% 7.92/1.49  fof(f9,axiom,(
% 7.92/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f23,plain,(
% 7.92/1.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.92/1.49    inference(ennf_transformation,[],[f9])).
% 7.92/1.49  
% 7.92/1.49  fof(f48,plain,(
% 7.92/1.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f23])).
% 7.92/1.49  
% 7.92/1.49  fof(f11,axiom,(
% 7.92/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f25,plain,(
% 7.92/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.92/1.49    inference(ennf_transformation,[],[f11])).
% 7.92/1.49  
% 7.92/1.49  fof(f50,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f25])).
% 7.92/1.49  
% 7.92/1.49  fof(f8,axiom,(
% 7.92/1.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f47,plain,(
% 7.92/1.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f8])).
% 7.92/1.49  
% 7.92/1.49  fof(f6,axiom,(
% 7.92/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f45,plain,(
% 7.92/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.92/1.49    inference(cnf_transformation,[],[f6])).
% 7.92/1.49  
% 7.92/1.49  fof(f12,axiom,(
% 7.92/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f26,plain,(
% 7.92/1.49    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.92/1.49    inference(ennf_transformation,[],[f12])).
% 7.92/1.49  
% 7.92/1.49  fof(f51,plain,(
% 7.92/1.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.92/1.49    inference(cnf_transformation,[],[f26])).
% 7.92/1.49  
% 7.92/1.49  fof(f4,axiom,(
% 7.92/1.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f43,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f4])).
% 7.92/1.49  
% 7.92/1.49  fof(f61,plain,(
% 7.92/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 7.92/1.49    inference(definition_unfolding,[],[f43,f41,f41])).
% 7.92/1.49  
% 7.92/1.49  fof(f60,plain,(
% 7.92/1.49    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) | ~v4_pre_topc(sK2,sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f38])).
% 7.92/1.49  
% 7.92/1.49  fof(f15,axiom,(
% 7.92/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 7.92/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.92/1.49  
% 7.92/1.49  fof(f28,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(ennf_transformation,[],[f15])).
% 7.92/1.49  
% 7.92/1.49  fof(f33,plain,(
% 7.92/1.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.92/1.49    inference(nnf_transformation,[],[f28])).
% 7.92/1.49  
% 7.92/1.49  fof(f55,plain,(
% 7.92/1.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f33])).
% 7.92/1.49  
% 7.92/1.49  fof(f59,plain,(
% 7.92/1.49    v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) | v4_pre_topc(sK2,sK1)),
% 7.92/1.49    inference(cnf_transformation,[],[f38])).
% 7.92/1.49  
% 7.92/1.49  fof(f54,plain,(
% 7.92/1.49    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.92/1.49    inference(cnf_transformation,[],[f33])).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2,plain,
% 7.92/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3,plain,
% 7.92/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_264,plain,
% 7.92/1.49      ( r2_hidden(sK0(X0,X1),X0) | k3_xboole_0(X0,X1) = X0 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_2,c_3]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_815,plain,
% 7.92/1.49      ( k3_xboole_0(X0,X1) = X0
% 7.92/1.49      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_19,negated_conjecture,
% 7.92/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.92/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_816,plain,
% 7.92/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_16,plain,
% 7.92/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_13,plain,
% 7.92/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_250,plain,
% 7.92/1.49      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_16,c_13]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_20,negated_conjecture,
% 7.92/1.49      ( l1_pre_topc(sK1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_292,plain,
% 7.92/1.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_250,c_20]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_293,plain,
% 7.92/1.49      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_292]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_823,plain,
% 7.92/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_816,c_293]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9,plain,
% 7.92/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.92/1.49      | ~ r2_hidden(X2,X0)
% 7.92/1.49      | r2_hidden(X2,X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_819,plain,
% 7.92/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.92/1.49      | r2_hidden(X2,X0) != iProver_top
% 7.92/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_989,plain,
% 7.92/1.49      ( r2_hidden(X0,k2_struct_0(sK1)) = iProver_top
% 7.92/1.49      | r2_hidden(X0,sK2) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_823,c_819]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1,plain,
% 7.92/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_275,plain,
% 7.92/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.92/1.49      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_814,plain,
% 7.92/1.49      ( k3_xboole_0(X0,X1) = X0
% 7.92/1.49      | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1197,plain,
% 7.92/1.49      ( k3_xboole_0(X0,k2_struct_0(sK1)) = X0
% 7.92/1.49      | r2_hidden(sK0(X0,k2_struct_0(sK1)),sK2) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_989,c_814]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3253,plain,
% 7.92/1.49      ( k3_xboole_0(sK2,k2_struct_0(sK1)) = sK2 ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_815,c_1197]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_4,plain,
% 7.92/1.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_12,plain,
% 7.92/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1049,plain,
% 7.92/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_4,c_12]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1104,plain,
% 7.92/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1049,c_12]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_6,plain,
% 7.92/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.92/1.49      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_822,plain,
% 7.92/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 7.92/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1436,plain,
% 7.92/1.49      ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),sK2)) = k3_subset_1(k2_struct_0(sK1),sK2) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_823,c_822]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1592,plain,
% 7.92/1.49      ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(sK2,k2_struct_0(sK1))) = k3_subset_1(k2_struct_0(sK1),sK2) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1104,c_1436]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3264,plain,
% 7.92/1.49      ( k3_subset_1(k2_struct_0(sK1),sK2) = k5_xboole_0(k2_struct_0(sK1),sK2) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_3253,c_1592]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_8,plain,
% 7.92/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.92/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.92/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_820,plain,
% 7.92/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.92/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3379,plain,
% 7.92/1.49      ( m1_subset_1(k5_xboole_0(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top
% 7.92/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_3264,c_820]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_10842,plain,
% 7.92/1.49      ( m1_subset_1(k5_xboole_0(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 7.92/1.49      inference(global_propositional_subsumption,
% 7.92/1.49                [status(thm)],
% 7.92/1.49                [c_3379,c_823]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_10,plain,
% 7.92/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.92/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_818,plain,
% 7.92/1.49      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 7.92/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_10851,plain,
% 7.92/1.49      ( k9_subset_1(k2_struct_0(sK1),X0,k5_xboole_0(k2_struct_0(sK1),sK2)) = k3_xboole_0(X0,k5_xboole_0(k2_struct_0(sK1),sK2)) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_10842,c_818]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_7,plain,
% 7.92/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.92/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_821,plain,
% 7.92/1.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_5,plain,
% 7.92/1.49      ( k2_subset_1(X0) = X0 ),
% 7.92/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_824,plain,
% 7.92/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_821,c_5]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_11,plain,
% 7.92/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.92/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.92/1.49      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.92/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_817,plain,
% 7.92/1.49      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 7.92/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.92/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_2628,plain,
% 7.92/1.49      ( k9_subset_1(X0,X0,k3_subset_1(X0,X1)) = k7_subset_1(X0,X0,X1)
% 7.92/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_824,c_817]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9625,plain,
% 7.92/1.49      ( k9_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_823,c_2628]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_9631,plain,
% 7.92/1.49      ( k9_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),k5_xboole_0(k2_struct_0(sK1),sK2)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_9625,c_3264]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_10869,plain,
% 7.92/1.49      ( k3_xboole_0(k2_struct_0(sK1),k5_xboole_0(k2_struct_0(sK1),sK2)) = k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_10851,c_9631]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_0,plain,
% 7.92/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1595,plain,
% 7.92/1.49      ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2))) = k3_xboole_0(k2_struct_0(sK1),sK2) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1436,c_0]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1660,plain,
% 7.92/1.49      ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),sK2))) = k3_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2)) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1595,c_0]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_1704,plain,
% 7.92/1.49      ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),k3_xboole_0(sK2,k2_struct_0(sK1)))) = k3_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2)) ),
% 7.92/1.49      inference(superposition,[status(thm)],[c_1104,c_1660]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3260,plain,
% 7.92/1.49      ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),sK2)) = k3_xboole_0(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),sK2)) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_3253,c_1704]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3269,plain,
% 7.92/1.49      ( k5_xboole_0(k2_struct_0(sK1),k3_xboole_0(k2_struct_0(sK1),sK2)) = k3_xboole_0(k2_struct_0(sK1),k5_xboole_0(k2_struct_0(sK1),sK2)) ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_3260,c_3264]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3270,plain,
% 7.92/1.49      ( k3_xboole_0(k2_struct_0(sK1),k5_xboole_0(k2_struct_0(sK1),sK2)) = k3_subset_1(k2_struct_0(sK1),sK2) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_3269,c_1436]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3326,plain,
% 7.92/1.49      ( k3_xboole_0(k2_struct_0(sK1),k5_xboole_0(k2_struct_0(sK1),sK2)) = k5_xboole_0(k2_struct_0(sK1),sK2) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_3270,c_3264,c_3270]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_10870,plain,
% 7.92/1.49      ( k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2) = k5_xboole_0(k2_struct_0(sK1),sK2) ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_10869,c_3326]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_17,negated_conjecture,
% 7.92/1.49      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | ~ v4_pre_topc(sK2,sK1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_144,plain,
% 7.92/1.49      ( ~ v4_pre_topc(sK2,sK1)
% 7.92/1.49      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
% 7.92/1.49      inference(prop_impl,[status(thm)],[c_17]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_145,plain,
% 7.92/1.49      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | ~ v4_pre_topc(sK2,sK1) ),
% 7.92/1.49      inference(renaming,[status(thm)],[c_144]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_14,plain,
% 7.92/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 7.92/1.49      | v4_pre_topc(X1,X0)
% 7.92/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.92/1.49      | ~ l1_pre_topc(X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_312,plain,
% 7.92/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 7.92/1.49      | v4_pre_topc(X1,X0)
% 7.92/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.92/1.49      | sK1 != X0 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_313,plain,
% 7.92/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
% 7.92/1.49      | v4_pre_topc(X0,sK1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_312]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_352,plain,
% 7.92/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
% 7.92/1.49      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.92/1.49      | sK2 != X0
% 7.92/1.49      | sK1 != sK1 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_145,c_313]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_353,plain,
% 7.92/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_352]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_412,plain,
% 7.92/1.49      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) ),
% 7.92/1.49      inference(prop_impl,[status(thm)],[c_19,c_353]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_413,plain,
% 7.92/1.49      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
% 7.92/1.49      inference(renaming,[status(thm)],[c_412]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_812,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
% 7.92/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) != iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_826,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
% 7.92/1.49      | v3_pre_topc(k3_subset_1(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_812,c_293]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3373,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) != iProver_top
% 7.92/1.49      | v3_pre_topc(k5_xboole_0(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_3264,c_826]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_15451,plain,
% 7.92/1.49      ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK1),sK2),sK1) != iProver_top ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_10870,c_3373]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_18,negated_conjecture,
% 7.92/1.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | v4_pre_topc(sK2,sK1) ),
% 7.92/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_146,plain,
% 7.92/1.49      ( v4_pre_topc(sK2,sK1)
% 7.92/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
% 7.92/1.49      inference(prop_impl,[status(thm)],[c_18]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_147,plain,
% 7.92/1.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | v4_pre_topc(sK2,sK1) ),
% 7.92/1.49      inference(renaming,[status(thm)],[c_146]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_15,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 7.92/1.49      | ~ v4_pre_topc(X1,X0)
% 7.92/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.92/1.49      | ~ l1_pre_topc(X0) ),
% 7.92/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_297,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 7.92/1.49      | ~ v4_pre_topc(X1,X0)
% 7.92/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.92/1.49      | sK1 != X0 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_298,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
% 7.92/1.49      | ~ v4_pre_topc(X0,sK1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_297]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_338,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0),sK1)
% 7.92/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.92/1.49      | sK2 != X0
% 7.92/1.49      | sK1 != sK1 ),
% 7.92/1.49      inference(resolution_lifted,[status(thm)],[c_147,c_298]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_339,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.92/1.49      inference(unflattening,[status(thm)],[c_338]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_414,plain,
% 7.92/1.49      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) ),
% 7.92/1.49      inference(prop_impl,[status(thm)],[c_19,c_339]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_415,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1)
% 7.92/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
% 7.92/1.49      inference(renaming,[status(thm)],[c_414]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_813,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
% 7.92/1.49      | v3_pre_topc(k3_subset_1(u1_struct_0(sK1),sK2),sK1) = iProver_top ),
% 7.92/1.49      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_825,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
% 7.92/1.49      | v3_pre_topc(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
% 7.92/1.49      inference(light_normalisation,[status(thm)],[c_813,c_293]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_3372,plain,
% 7.92/1.49      ( v3_pre_topc(k7_subset_1(k2_struct_0(sK1),k2_struct_0(sK1),sK2),sK1) = iProver_top
% 7.92/1.49      | v3_pre_topc(k5_xboole_0(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_3264,c_825]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(c_15450,plain,
% 7.92/1.49      ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
% 7.92/1.49      inference(demodulation,[status(thm)],[c_10870,c_3372]) ).
% 7.92/1.49  
% 7.92/1.49  cnf(contradiction,plain,
% 7.92/1.49      ( $false ),
% 7.92/1.49      inference(minisat,[status(thm)],[c_15451,c_15450]) ).
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.92/1.49  
% 7.92/1.49  ------                               Statistics
% 7.92/1.49  
% 7.92/1.49  ------ General
% 7.92/1.49  
% 7.92/1.49  abstr_ref_over_cycles:                  0
% 7.92/1.49  abstr_ref_under_cycles:                 0
% 7.92/1.49  gc_basic_clause_elim:                   0
% 7.92/1.49  forced_gc_time:                         0
% 7.92/1.49  parsing_time:                           0.013
% 7.92/1.49  unif_index_cands_time:                  0.
% 7.92/1.49  unif_index_add_time:                    0.
% 7.92/1.49  orderings_time:                         0.
% 7.92/1.49  out_proof_time:                         0.009
% 7.92/1.49  total_time:                             0.829
% 7.92/1.49  num_of_symbols:                         52
% 7.92/1.49  num_of_terms:                           19800
% 7.92/1.49  
% 7.92/1.49  ------ Preprocessing
% 7.92/1.49  
% 7.92/1.49  num_of_splits:                          0
% 7.92/1.49  num_of_split_atoms:                     0
% 7.92/1.49  num_of_reused_defs:                     0
% 7.92/1.49  num_eq_ax_congr_red:                    35
% 7.92/1.49  num_of_sem_filtered_clauses:            1
% 7.92/1.49  num_of_subtypes:                        0
% 7.92/1.49  monotx_restored_types:                  0
% 7.92/1.49  sat_num_of_epr_types:                   0
% 7.92/1.49  sat_num_of_non_cyclic_types:            0
% 7.92/1.49  sat_guarded_non_collapsed_types:        0
% 7.92/1.49  num_pure_diseq_elim:                    0
% 7.92/1.49  simp_replaced_by:                       0
% 7.92/1.49  res_preprocessed:                       98
% 7.92/1.49  prep_upred:                             0
% 7.92/1.49  prep_unflattend:                        5
% 7.92/1.49  smt_new_axioms:                         0
% 7.92/1.49  pred_elim_cands:                        3
% 7.92/1.49  pred_elim:                              4
% 7.92/1.49  pred_elim_cl:                           5
% 7.92/1.49  pred_elim_cycles:                       6
% 7.92/1.49  merged_defs:                            8
% 7.92/1.49  merged_defs_ncl:                        0
% 7.92/1.49  bin_hyper_res:                          8
% 7.92/1.49  prep_cycles:                            4
% 7.92/1.49  pred_elim_time:                         0.002
% 7.92/1.49  splitting_time:                         0.
% 7.92/1.49  sem_filter_time:                        0.
% 7.92/1.49  monotx_time:                            0.
% 7.92/1.49  subtype_inf_time:                       0.
% 7.92/1.49  
% 7.92/1.49  ------ Problem properties
% 7.92/1.49  
% 7.92/1.49  clauses:                                16
% 7.92/1.49  conjectures:                            1
% 7.92/1.49  epr:                                    0
% 7.92/1.49  horn:                                   14
% 7.92/1.49  ground:                                 4
% 7.92/1.49  unary:                                  7
% 7.92/1.49  binary:                                 7
% 7.92/1.49  lits:                                   27
% 7.92/1.49  lits_eq:                                10
% 7.92/1.49  fd_pure:                                0
% 7.92/1.49  fd_pseudo:                              0
% 7.92/1.49  fd_cond:                                0
% 7.92/1.49  fd_pseudo_cond:                         0
% 7.92/1.49  ac_symbols:                             0
% 7.92/1.49  
% 7.92/1.49  ------ Propositional Solver
% 7.92/1.49  
% 7.92/1.49  prop_solver_calls:                      35
% 7.92/1.49  prop_fast_solver_calls:                 654
% 7.92/1.49  smt_solver_calls:                       0
% 7.92/1.49  smt_fast_solver_calls:                  0
% 7.92/1.49  prop_num_of_clauses:                    4332
% 7.92/1.49  prop_preprocess_simplified:             9480
% 7.92/1.49  prop_fo_subsumed:                       5
% 7.92/1.49  prop_solver_time:                       0.
% 7.92/1.49  smt_solver_time:                        0.
% 7.92/1.49  smt_fast_solver_time:                   0.
% 7.92/1.49  prop_fast_solver_time:                  0.
% 7.92/1.49  prop_unsat_core_time:                   0.
% 7.92/1.49  
% 7.92/1.49  ------ QBF
% 7.92/1.49  
% 7.92/1.49  qbf_q_res:                              0
% 7.92/1.49  qbf_num_tautologies:                    0
% 7.92/1.49  qbf_prep_cycles:                        0
% 7.92/1.49  
% 7.92/1.49  ------ BMC1
% 7.92/1.49  
% 7.92/1.49  bmc1_current_bound:                     -1
% 7.92/1.49  bmc1_last_solved_bound:                 -1
% 7.92/1.49  bmc1_unsat_core_size:                   -1
% 7.92/1.49  bmc1_unsat_core_parents_size:           -1
% 7.92/1.49  bmc1_merge_next_fun:                    0
% 7.92/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.92/1.49  
% 7.92/1.49  ------ Instantiation
% 7.92/1.49  
% 7.92/1.49  inst_num_of_clauses:                    1802
% 7.92/1.49  inst_num_in_passive:                    458
% 7.92/1.49  inst_num_in_active:                     774
% 7.92/1.49  inst_num_in_unprocessed:                570
% 7.92/1.49  inst_num_of_loops:                      880
% 7.92/1.49  inst_num_of_learning_restarts:          0
% 7.92/1.49  inst_num_moves_active_passive:          98
% 7.92/1.49  inst_lit_activity:                      0
% 7.92/1.49  inst_lit_activity_moves:                0
% 7.92/1.49  inst_num_tautologies:                   0
% 7.92/1.49  inst_num_prop_implied:                  0
% 7.92/1.49  inst_num_existing_simplified:           0
% 7.92/1.49  inst_num_eq_res_simplified:             0
% 7.92/1.49  inst_num_child_elim:                    0
% 7.92/1.49  inst_num_of_dismatching_blockings:      895
% 7.92/1.49  inst_num_of_non_proper_insts:           1965
% 7.92/1.49  inst_num_of_duplicates:                 0
% 7.92/1.49  inst_inst_num_from_inst_to_res:         0
% 7.92/1.49  inst_dismatching_checking_time:         0.
% 7.92/1.49  
% 7.92/1.49  ------ Resolution
% 7.92/1.49  
% 7.92/1.49  res_num_of_clauses:                     0
% 7.92/1.49  res_num_in_passive:                     0
% 7.92/1.49  res_num_in_active:                      0
% 7.92/1.49  res_num_of_loops:                       102
% 7.92/1.49  res_forward_subset_subsumed:            303
% 7.92/1.49  res_backward_subset_subsumed:           0
% 7.92/1.49  res_forward_subsumed:                   0
% 7.92/1.49  res_backward_subsumed:                  0
% 7.92/1.49  res_forward_subsumption_resolution:     0
% 7.92/1.49  res_backward_subsumption_resolution:    0
% 7.92/1.49  res_clause_to_clause_subsumption:       8300
% 7.92/1.49  res_orphan_elimination:                 0
% 7.92/1.49  res_tautology_del:                      289
% 7.92/1.49  res_num_eq_res_simplified:              0
% 7.92/1.49  res_num_sel_changes:                    0
% 7.92/1.49  res_moves_from_active_to_pass:          0
% 7.92/1.49  
% 7.92/1.49  ------ Superposition
% 7.92/1.49  
% 7.92/1.49  sup_time_total:                         0.
% 7.92/1.49  sup_time_generating:                    0.
% 7.92/1.49  sup_time_sim_full:                      0.
% 7.92/1.49  sup_time_sim_immed:                     0.
% 7.92/1.49  
% 7.92/1.49  sup_num_of_clauses:                     860
% 7.92/1.49  sup_num_in_active:                      103
% 7.92/1.49  sup_num_in_passive:                     757
% 7.92/1.49  sup_num_of_loops:                       174
% 7.92/1.49  sup_fw_superposition:                   1744
% 7.92/1.49  sup_bw_superposition:                   1991
% 7.92/1.49  sup_immediate_simplified:               3174
% 7.92/1.49  sup_given_eliminated:                   9
% 7.92/1.49  comparisons_done:                       0
% 7.92/1.49  comparisons_avoided:                    0
% 7.92/1.49  
% 7.92/1.49  ------ Simplifications
% 7.92/1.49  
% 7.92/1.49  
% 7.92/1.49  sim_fw_subset_subsumed:                 3
% 7.92/1.49  sim_bw_subset_subsumed:                 2
% 7.92/1.49  sim_fw_subsumed:                        31
% 7.92/1.49  sim_bw_subsumed:                        4
% 7.92/1.49  sim_fw_subsumption_res:                 0
% 7.92/1.49  sim_bw_subsumption_res:                 0
% 7.92/1.49  sim_tautology_del:                      4
% 7.92/1.49  sim_eq_tautology_del:                   1549
% 7.92/1.49  sim_eq_res_simp:                        0
% 7.92/1.49  sim_fw_demodulated:                     1473
% 7.92/1.49  sim_bw_demodulated:                     284
% 7.92/1.49  sim_light_normalised:                   1967
% 7.92/1.49  sim_joinable_taut:                      0
% 7.92/1.49  sim_joinable_simp:                      0
% 7.92/1.49  sim_ac_normalised:                      0
% 7.92/1.49  sim_smt_subsumption:                    0
% 7.92/1.49  
%------------------------------------------------------------------------------
