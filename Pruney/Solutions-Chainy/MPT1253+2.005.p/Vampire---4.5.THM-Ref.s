%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:23 EST 2020

% Result     : Theorem 2.75s
% Output     : Refutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 228 expanded)
%              Number of leaves         :   20 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  264 ( 744 expanded)
%              Number of equality atoms :   42 (  67 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1205,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1197,f1091])).

fof(f1091,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f110,f1085])).

fof(f1085,plain,(
    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f1070,f59])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f1070,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(sK0,X1))) ) ),
    inference(subsumption_resolution,[],[f1066,f443])).

fof(f443,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f429,f417])).

fof(f417,plain,(
    ! [X0] :
      ( k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f62,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f429,plain,(
    ! [X1] :
      ( m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f427,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f74,f68])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f427,plain,(
    ! [X0] : m1_subset_1(k2_tops_1(sK0,k6_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f426,f58])).

fof(f426,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tops_1(sK0,k6_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f425,f126])).

fof(f126,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f66,f95])).

fof(f95,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f71,f70,f68,f68])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f425,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tops_1(sK0,k6_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f77,f422])).

fof(f422,plain,(
    ! [X0] : k2_tops_1(sK0,k6_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0))) ),
    inference(subsumption_resolution,[],[f420,f66])).

fof(f420,plain,(
    ! [X0] :
      ( k2_tops_1(sK0,k6_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)))
      | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f417,f137])).

fof(f137,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(subsumption_resolution,[],[f133,f66])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1))
      | ~ m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f97,f95])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f1066,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(sK0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k2_tops_1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f1059])).

fof(f1059,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(sK0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k2_tops_1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f600,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f87,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f600,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f63,f58])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f110,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f94,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1197,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f1191,f241])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(k2_tops_1(sK0,sK1),X0) ) ),
    inference(resolution,[],[f240,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f240,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | ~ r1_tarski(k2_tops_1(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f236,f61])).

fof(f61,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f236,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | ~ r1_tarski(k2_tops_1(sK0,sK1),X0)
      | r1_tarski(k2_tops_1(sK0,sK1),sK1) ) ),
    inference(resolution,[],[f170,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f170,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | ~ r1_tarski(X5,X4) ) ),
    inference(resolution,[],[f153,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f153,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK1)) ) ),
    inference(resolution,[],[f148,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),X0) ) ),
    inference(resolution,[],[f122,f61])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(sK2(X0,X1),X2) ) ),
    inference(resolution,[],[f81,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1191,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f1188,f59])).

fof(f1188,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f1177,f105])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1177,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f1176,f59])).

fof(f1176,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X0),sK1) ) ),
    inference(resolution,[],[f903,f60])).

fof(f60,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f903,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,sK0)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X0),X1) ) ),
    inference(resolution,[],[f64,f58])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:29:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (2387)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (2371)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (2368)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (2377)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (2367)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (2370)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (2391)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.58  % (2369)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.58  % (2375)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.58  % (2373)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.59  % (2365)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.59  % (2386)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.59  % (2384)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.59  % (2366)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.59  % (2378)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.59  % (2392)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.60  % (2379)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.60  % (2388)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.60  % (2380)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.60  % (2389)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.60  % (2394)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.60  % (2382)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.61  % (2381)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.61  % (2372)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.61  % (2383)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.76/0.61  % (2393)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.76/0.62  % (2374)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.76/0.62  % (2390)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.76/0.63  % (2382)Refutation not found, incomplete strategy% (2382)------------------------------
% 1.76/0.63  % (2382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.63  % (2382)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.63  
% 1.76/0.63  % (2382)Memory used [KB]: 10746
% 1.76/0.63  % (2382)Time elapsed: 0.201 s
% 1.76/0.63  % (2382)------------------------------
% 1.76/0.63  % (2382)------------------------------
% 2.02/0.63  % (2385)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.02/0.64  % (2376)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.75/0.76  % (2368)Refutation found. Thanks to Tanya!
% 2.75/0.76  % SZS status Theorem for theBenchmark
% 2.75/0.76  % SZS output start Proof for theBenchmark
% 2.75/0.76  fof(f1205,plain,(
% 2.75/0.76    $false),
% 2.75/0.76    inference(subsumption_resolution,[],[f1197,f1091])).
% 2.75/0.76  fof(f1091,plain,(
% 2.75/0.76    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 2.75/0.76    inference(superposition,[],[f110,f1085])).
% 2.75/0.76  fof(f1085,plain,(
% 2.75/0.76    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.75/0.76    inference(resolution,[],[f1070,f59])).
% 2.75/0.76  fof(f59,plain,(
% 2.75/0.76    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.75/0.76    inference(cnf_transformation,[],[f45])).
% 2.75/0.76  fof(f45,plain,(
% 2.75/0.76    (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.75/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f44,f43])).
% 2.75/0.76  fof(f43,plain,(
% 2.75/0.76    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.75/0.76    introduced(choice_axiom,[])).
% 2.75/0.76  fof(f44,plain,(
% 2.75/0.76    ? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.75/0.76    introduced(choice_axiom,[])).
% 2.75/0.76  fof(f26,plain,(
% 2.75/0.76    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.75/0.76    inference(flattening,[],[f25])).
% 2.75/0.76  fof(f25,plain,(
% 2.75/0.76    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.75/0.76    inference(ennf_transformation,[],[f24])).
% 2.75/0.76  fof(f24,negated_conjecture,(
% 2.75/0.76    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.75/0.76    inference(negated_conjecture,[],[f23])).
% 2.75/0.76  fof(f23,conjecture,(
% 2.75/0.76    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.75/0.76  fof(f1070,plain,(
% 2.75/0.76    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(sK0,X1)))) )),
% 2.75/0.76    inference(subsumption_resolution,[],[f1066,f443])).
% 2.75/0.76  fof(f443,plain,(
% 2.75/0.76    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.75/0.76    inference(duplicate_literal_removal,[],[f442])).
% 2.75/0.76  fof(f442,plain,(
% 2.75/0.76    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.75/0.76    inference(superposition,[],[f429,f417])).
% 2.75/0.76  fof(f417,plain,(
% 2.75/0.76    ( ! [X0] : (k2_tops_1(sK0,X0) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.75/0.76    inference(resolution,[],[f62,f58])).
% 2.75/0.76  fof(f58,plain,(
% 2.75/0.76    l1_pre_topc(sK0)),
% 2.75/0.76    inference(cnf_transformation,[],[f45])).
% 2.75/0.76  fof(f62,plain,(
% 2.75/0.76    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 2.75/0.76    inference(cnf_transformation,[],[f27])).
% 2.75/0.76  fof(f27,plain,(
% 2.75/0.76    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.75/0.76    inference(ennf_transformation,[],[f21])).
% 2.75/0.76  fof(f21,axiom,(
% 2.75/0.76    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 2.75/0.76  fof(f429,plain,(
% 2.75/0.76    ( ! [X1] : (m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.75/0.76    inference(superposition,[],[f427,f97])).
% 2.75/0.76  fof(f97,plain,(
% 2.75/0.76    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k6_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.75/0.76    inference(definition_unfolding,[],[f74,f68])).
% 2.75/0.76  fof(f68,plain,(
% 2.75/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.75/0.76    inference(cnf_transformation,[],[f14])).
% 2.75/0.76  fof(f14,axiom,(
% 2.75/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.75/0.76  fof(f74,plain,(
% 2.75/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.75/0.76    inference(cnf_transformation,[],[f32])).
% 2.75/0.76  fof(f32,plain,(
% 2.75/0.76    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.75/0.76    inference(ennf_transformation,[],[f9])).
% 2.75/0.76  fof(f9,axiom,(
% 2.75/0.76    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.75/0.76  fof(f427,plain,(
% 2.75/0.76    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,k6_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.75/0.76    inference(subsumption_resolution,[],[f426,f58])).
% 2.75/0.76  fof(f426,plain,(
% 2.75/0.76    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,k6_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.75/0.76    inference(subsumption_resolution,[],[f425,f126])).
% 2.75/0.76  fof(f126,plain,(
% 2.75/0.76    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0))) )),
% 2.75/0.76    inference(superposition,[],[f66,f95])).
% 2.75/0.76  fof(f95,plain,(
% 2.75/0.76    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.75/0.76    inference(definition_unfolding,[],[f71,f70,f68,f68])).
% 2.75/0.76  fof(f70,plain,(
% 2.75/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.75/0.76    inference(cnf_transformation,[],[f17])).
% 2.75/0.76  fof(f17,axiom,(
% 2.75/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.75/0.76  fof(f71,plain,(
% 2.75/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.75/0.76    inference(cnf_transformation,[],[f5])).
% 2.75/0.76  fof(f5,axiom,(
% 2.75/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.75/0.76  fof(f66,plain,(
% 2.75/0.76    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.75/0.76    inference(cnf_transformation,[],[f12])).
% 2.75/0.76  fof(f12,axiom,(
% 2.75/0.76    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.75/0.76  fof(f425,plain,(
% 2.75/0.76    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,k6_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.75/0.76    inference(superposition,[],[f77,f422])).
% 2.75/0.76  fof(f422,plain,(
% 2.75/0.76    ( ! [X0] : (k2_tops_1(sK0,k6_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)))) )),
% 2.75/0.76    inference(subsumption_resolution,[],[f420,f66])).
% 2.75/0.76  fof(f420,plain,(
% 2.75/0.76    ( ! [X0] : (k2_tops_1(sK0,k6_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0))) | ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.75/0.76    inference(superposition,[],[f417,f137])).
% 2.75/0.76  fof(f137,plain,(
% 2.75/0.76    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.75/0.76    inference(subsumption_resolution,[],[f133,f66])).
% 2.75/0.76  fof(f133,plain,(
% 2.75/0.76    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1)) | ~m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.75/0.76    inference(superposition,[],[f97,f95])).
% 2.75/0.76  fof(f77,plain,(
% 2.75/0.76    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.75/0.76    inference(cnf_transformation,[],[f37])).
% 2.75/0.76  fof(f37,plain,(
% 2.75/0.76    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.75/0.76    inference(flattening,[],[f36])).
% 2.75/0.76  fof(f36,plain,(
% 2.75/0.76    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.75/0.76    inference(ennf_transformation,[],[f19])).
% 2.75/0.76  fof(f19,axiom,(
% 2.75/0.76    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.75/0.76  fof(f1066,plain,(
% 2.75/0.76    ( ! [X1] : (k2_pre_topc(sK0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.75/0.76    inference(duplicate_literal_removal,[],[f1059])).
% 2.75/0.76  fof(f1059,plain,(
% 2.75/0.76    ( ! [X1] : (k2_pre_topc(sK0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(sK0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.75/0.76    inference(superposition,[],[f600,f98])).
% 2.75/0.76  fof(f98,plain,(
% 2.75/0.76    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.75/0.76    inference(definition_unfolding,[],[f87,f69])).
% 2.75/0.76  fof(f69,plain,(
% 2.75/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.75/0.76    inference(cnf_transformation,[],[f8])).
% 2.75/0.76  fof(f8,axiom,(
% 2.75/0.76    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.75/0.76  fof(f87,plain,(
% 2.75/0.76    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.75/0.76    inference(cnf_transformation,[],[f42])).
% 2.75/0.76  fof(f42,plain,(
% 2.75/0.76    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.75/0.76    inference(flattening,[],[f41])).
% 2.75/0.76  fof(f41,plain,(
% 2.75/0.76    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.75/0.76    inference(ennf_transformation,[],[f13])).
% 2.75/0.76  fof(f13,axiom,(
% 2.75/0.76    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.75/0.76  fof(f600,plain,(
% 2.75/0.76    ( ! [X0] : (k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.75/0.76    inference(resolution,[],[f63,f58])).
% 2.75/0.76  fof(f63,plain,(
% 2.75/0.76    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.75/0.76    inference(cnf_transformation,[],[f28])).
% 2.75/0.76  fof(f28,plain,(
% 2.75/0.76    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.75/0.76    inference(ennf_transformation,[],[f22])).
% 2.75/0.76  fof(f22,axiom,(
% 2.75/0.76    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.75/0.76  fof(f110,plain,(
% 2.75/0.76    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 2.75/0.76    inference(superposition,[],[f94,f67])).
% 2.75/0.76  fof(f67,plain,(
% 2.75/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.75/0.76    inference(cnf_transformation,[],[f7])).
% 2.75/0.76  fof(f7,axiom,(
% 2.75/0.76    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.75/0.76  fof(f94,plain,(
% 2.75/0.76    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 2.75/0.76    inference(definition_unfolding,[],[f65,f69])).
% 2.75/0.76  fof(f65,plain,(
% 2.75/0.76    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.75/0.76    inference(cnf_transformation,[],[f6])).
% 2.75/0.76  fof(f6,axiom,(
% 2.75/0.76    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.75/0.76  fof(f1197,plain,(
% 2.75/0.76    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 2.75/0.76    inference(resolution,[],[f1191,f241])).
% 2.75/0.76  fof(f241,plain,(
% 2.75/0.76    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(k2_tops_1(sK0,sK1),X0)) )),
% 2.75/0.76    inference(resolution,[],[f240,f85])).
% 2.75/0.76  fof(f85,plain,(
% 2.75/0.76    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.75/0.76    inference(cnf_transformation,[],[f52])).
% 2.75/0.76  fof(f52,plain,(
% 2.75/0.76    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.75/0.76    inference(nnf_transformation,[],[f18])).
% 2.75/0.76  fof(f18,axiom,(
% 2.75/0.76    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.75/0.76  fof(f240,plain,(
% 2.75/0.76    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r1_tarski(k2_tops_1(sK0,sK1),X0)) )),
% 2.75/0.76    inference(subsumption_resolution,[],[f236,f61])).
% 2.75/0.76  fof(f61,plain,(
% 2.75/0.76    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.75/0.76    inference(cnf_transformation,[],[f45])).
% 2.75/0.76  fof(f236,plain,(
% 2.75/0.76    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r1_tarski(k2_tops_1(sK0,sK1),X0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)) )),
% 2.75/0.76    inference(resolution,[],[f170,f82])).
% 2.75/0.76  fof(f82,plain,(
% 2.75/0.76    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.75/0.76    inference(cnf_transformation,[],[f51])).
% 2.75/0.76  fof(f51,plain,(
% 2.75/0.76    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.75/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 2.75/0.76  fof(f50,plain,(
% 2.75/0.76    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.75/0.76    introduced(choice_axiom,[])).
% 2.75/0.76  fof(f49,plain,(
% 2.75/0.76    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.75/0.76    inference(rectify,[],[f48])).
% 2.75/0.76  fof(f48,plain,(
% 2.75/0.76    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.75/0.76    inference(nnf_transformation,[],[f38])).
% 2.75/0.76  fof(f38,plain,(
% 2.75/0.76    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.75/0.76    inference(ennf_transformation,[],[f1])).
% 2.75/0.76  fof(f1,axiom,(
% 2.75/0.76    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.75/0.76  fof(f170,plain,(
% 2.75/0.76    ( ! [X4,X5] : (~r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),X5) | ~m1_subset_1(X4,k1_zfmisc_1(sK1)) | ~r1_tarski(X5,X4)) )),
% 2.75/0.76    inference(resolution,[],[f153,f81])).
% 2.75/0.76  fof(f81,plain,(
% 2.75/0.76    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.75/0.76    inference(cnf_transformation,[],[f51])).
% 2.75/0.76  fof(f153,plain,(
% 2.75/0.76    ( ! [X2] : (~r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK1))) )),
% 2.75/0.76    inference(resolution,[],[f148,f84])).
% 2.75/0.76  fof(f84,plain,(
% 2.75/0.76    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.75/0.76    inference(cnf_transformation,[],[f52])).
% 2.75/0.76  fof(f148,plain,(
% 2.75/0.76    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK2(k2_tops_1(sK0,sK1),sK1),X0)) )),
% 2.75/0.76    inference(resolution,[],[f122,f61])).
% 2.75/0.76  fof(f122,plain,(
% 2.75/0.76    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r2_hidden(sK2(X0,X1),X2)) )),
% 2.75/0.76    inference(resolution,[],[f81,f83])).
% 2.75/0.76  fof(f83,plain,(
% 2.75/0.76    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.75/0.76    inference(cnf_transformation,[],[f51])).
% 2.75/0.76  fof(f1191,plain,(
% 2.75/0.76    r1_tarski(k2_pre_topc(sK0,sK1),sK1)),
% 2.75/0.76    inference(subsumption_resolution,[],[f1188,f59])).
% 2.75/0.76  fof(f1188,plain,(
% 2.75/0.76    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,sK1),sK1)),
% 2.75/0.76    inference(resolution,[],[f1177,f105])).
% 2.75/0.76  fof(f105,plain,(
% 2.75/0.76    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.75/0.76    inference(equality_resolution,[],[f79])).
% 2.75/0.76  fof(f79,plain,(
% 2.75/0.76    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.75/0.76    inference(cnf_transformation,[],[f47])).
% 2.75/0.76  fof(f47,plain,(
% 2.75/0.76    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.75/0.76    inference(flattening,[],[f46])).
% 2.75/0.76  fof(f46,plain,(
% 2.75/0.76    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.75/0.76    inference(nnf_transformation,[],[f3])).
% 2.75/0.76  fof(f3,axiom,(
% 2.75/0.76    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.75/0.76  fof(f1177,plain,(
% 2.75/0.76    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),sK1)) )),
% 2.75/0.76    inference(subsumption_resolution,[],[f1176,f59])).
% 2.75/0.76  fof(f1176,plain,(
% 2.75/0.76    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),sK1)) )),
% 2.75/0.76    inference(resolution,[],[f903,f60])).
% 2.75/0.76  fof(f60,plain,(
% 2.75/0.76    v4_pre_topc(sK1,sK0)),
% 2.75/0.76    inference(cnf_transformation,[],[f45])).
% 2.75/0.76  fof(f903,plain,(
% 2.75/0.76    ( ! [X0,X1] : (~v4_pre_topc(X1,sK0) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),X1)) )),
% 2.75/0.76    inference(resolution,[],[f64,f58])).
% 2.75/0.76  fof(f64,plain,(
% 2.75/0.76    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,X2),X1)) )),
% 2.75/0.76    inference(cnf_transformation,[],[f30])).
% 2.75/0.76  fof(f30,plain,(
% 2.75/0.76    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.75/0.76    inference(flattening,[],[f29])).
% 2.75/0.76  fof(f29,plain,(
% 2.75/0.76    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.75/0.76    inference(ennf_transformation,[],[f20])).
% 2.75/0.76  fof(f20,axiom,(
% 2.75/0.76    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 2.75/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).
% 2.75/0.76  % SZS output end Proof for theBenchmark
% 2.75/0.76  % (2368)------------------------------
% 2.75/0.76  % (2368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.76  % (2368)Termination reason: Refutation
% 2.75/0.76  
% 2.75/0.76  % (2368)Memory used [KB]: 11641
% 2.75/0.76  % (2368)Time elapsed: 0.324 s
% 2.75/0.76  % (2368)------------------------------
% 2.75/0.76  % (2368)------------------------------
% 2.75/0.76  % (2364)Success in time 0.391 s
%------------------------------------------------------------------------------
