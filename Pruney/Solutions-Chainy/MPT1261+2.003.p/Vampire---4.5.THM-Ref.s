%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:47 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :  118 (1588 expanded)
%              Number of leaves         :   20 ( 483 expanded)
%              Depth                    :   26
%              Number of atoms          :  267 (5637 expanded)
%              Number of equality atoms :   99 (1942 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1717,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1716,f1664])).

fof(f1664,plain,(
    k2_tops_1(sK0,sK1) != k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1660,f788])).

fof(f788,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f175,f759])).

fof(f759,plain,(
    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f121,f734])).

fof(f734,plain,(
    k1_tops_1(sK0,sK1) = k6_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(k1_tops_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f728,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f55,f51,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f728,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f72,f723])).

fof(f723,plain,(
    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f722,f169])).

fof(f169,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f62,f51])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f722,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f709,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f709,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f121,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X1,k6_subset_1(X1,X0))) ),
    inference(superposition,[],[f66,f65])).

fof(f65,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f52,f64,f64])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f51,f64])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f175,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f45,f169])).

fof(f45,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f1660,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f249,f1658])).

fof(f1658,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f1657])).

fof(f1657,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f1620,f1631])).

fof(f1631,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f800,f1622])).

fof(f1622,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f1620,f855])).

fof(f855,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f853,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f853,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f790,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f790,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f414,f759])).

fof(f414,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f413,f176])).

fof(f176,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f44,f169])).

fof(f44,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f413,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f405,f42])).

fof(f405,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f43])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f800,plain,(
    sK1 = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1)))) ),
    inference(superposition,[],[f77,f759])).

fof(f77,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k6_subset_1(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f76,f50])).

fof(f76,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k6_subset_1(X0,X1),X0)) = X0 ),
    inference(resolution,[],[f67,f72])).

fof(f1620,plain,(
    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1614,f573])).

fof(f573,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f563,f42])).

fof(f563,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f43])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f1614,plain,(
    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f1586,f454])).

fof(f454,plain,(
    k2_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f419,f427])).

fof(f427,plain,(
    k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f121,f335])).

fof(f335,plain,(
    k2_tops_1(sK0,sK1) = k6_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0))) ),
    inference(resolution,[],[f331,f68])).

fof(f331,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f326,f60])).

fof(f326,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f322,f42])).

fof(f322,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f43])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f419,plain,(
    k2_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f335,f65])).

fof(f1586,plain,(
    ! [X52] : k4_subset_1(u1_struct_0(sK0),sK1,k6_subset_1(u1_struct_0(sK0),X52)) = k3_tarski(k2_tarski(sK1,k6_subset_1(u1_struct_0(sK0),X52))) ),
    inference(resolution,[],[f507,f43])).

fof(f507,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | k4_subset_1(X5,X6,k6_subset_1(X5,X7)) = k3_tarski(k2_tarski(X6,k6_subset_1(X5,X7))) ) ),
    inference(resolution,[],[f70,f49])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f63,f53])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f249,plain,(
    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f248,f41])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f248,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f245,f42])).

fof(f245,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f58,f43])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f1716,plain,(
    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1697,f723])).

fof(f1697,plain,(
    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k6_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f117,f1666])).

fof(f1666,plain,(
    k2_tops_1(sK0,sK1) = k6_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_tops_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f1665,f68])).

fof(f1665,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f1660,f413])).

fof(f117,plain,(
    ! [X0,X1] : k6_subset_1(X1,k6_subset_1(X1,X0)) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X1,k6_subset_1(X1,X0)))) ),
    inference(superposition,[],[f66,f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:58:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (27331)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.45  % (27333)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (27336)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (27332)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (27320)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (27324)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (27326)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (27322)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (27321)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (27323)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (27329)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (27335)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (27327)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (27325)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.52  % (27328)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (27337)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (27334)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.53  % (27330)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.37/0.54  % (27332)Refutation found. Thanks to Tanya!
% 1.37/0.54  % SZS status Theorem for theBenchmark
% 1.37/0.54  % SZS output start Proof for theBenchmark
% 1.37/0.54  fof(f1717,plain,(
% 1.37/0.54    $false),
% 1.37/0.54    inference(subsumption_resolution,[],[f1716,f1664])).
% 1.37/0.54  fof(f1664,plain,(
% 1.37/0.54    k2_tops_1(sK0,sK1) != k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(resolution,[],[f1660,f788])).
% 1.37/0.54  fof(f788,plain,(
% 1.37/0.54    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(backward_demodulation,[],[f175,f759])).
% 1.37/0.54  fof(f759,plain,(
% 1.37/0.54    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(superposition,[],[f121,f734])).
% 1.37/0.54  fof(f734,plain,(
% 1.37/0.54    k1_tops_1(sK0,sK1) = k6_subset_1(k1_tops_1(sK0,sK1),k6_subset_1(k1_tops_1(sK0,sK1),sK1))),
% 1.37/0.54    inference(resolution,[],[f728,f68])).
% 1.37/0.54  fof(f68,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0) )),
% 1.37/0.54    inference(definition_unfolding,[],[f57,f64])).
% 1.37/0.54  fof(f64,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f55,f51,f51])).
% 1.37/0.54  fof(f51,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f10])).
% 1.37/0.54  fof(f10,axiom,(
% 1.37/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.37/0.54  fof(f55,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f5])).
% 1.37/0.54  fof(f5,axiom,(
% 1.37/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.37/0.54  fof(f57,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f27])).
% 1.37/0.54  fof(f27,plain,(
% 1.37/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.37/0.54  fof(f728,plain,(
% 1.37/0.54    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.37/0.54    inference(superposition,[],[f72,f723])).
% 1.37/0.54  fof(f723,plain,(
% 1.37/0.54    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 1.37/0.54    inference(superposition,[],[f722,f169])).
% 1.37/0.54  fof(f169,plain,(
% 1.37/0.54    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0)) )),
% 1.37/0.54    inference(resolution,[],[f69,f43])).
% 1.37/0.54  fof(f43,plain,(
% 1.37/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.54    inference(cnf_transformation,[],[f39])).
% 1.37/0.54  fof(f39,plain,(
% 1.37/0.54    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 1.37/0.54  fof(f37,plain,(
% 1.37/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f38,plain,(
% 1.37/0.54    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f36,plain,(
% 1.37/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.37/0.54    inference(flattening,[],[f35])).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.37/0.54    inference(nnf_transformation,[],[f21])).
% 1.37/0.54  fof(f21,plain,(
% 1.37/0.54    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.37/0.54    inference(flattening,[],[f20])).
% 1.37/0.54  fof(f20,plain,(
% 1.37/0.54    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f19])).
% 1.37/0.54  fof(f19,negated_conjecture,(
% 1.37/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.37/0.54    inference(negated_conjecture,[],[f18])).
% 1.37/0.54  fof(f18,conjecture,(
% 1.37/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 1.37/0.54  fof(f69,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f62,f51])).
% 1.37/0.54  fof(f62,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f32])).
% 1.37/0.54  fof(f32,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f11])).
% 1.37/0.54  fof(f11,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.37/0.54  fof(f722,plain,(
% 1.37/0.54    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.37/0.54    inference(subsumption_resolution,[],[f709,f42])).
% 1.37/0.54  fof(f42,plain,(
% 1.37/0.54    l1_pre_topc(sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f39])).
% 1.37/0.54  fof(f709,plain,(
% 1.37/0.54    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f47,f43])).
% 1.37/0.54  fof(f47,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f23])).
% 1.37/0.54  fof(f23,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f17])).
% 1.37/0.54  fof(f17,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.37/0.54  fof(f72,plain,(
% 1.37/0.54    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.37/0.54    inference(resolution,[],[f60,f49])).
% 1.37/0.54  fof(f49,plain,(
% 1.37/0.54    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f8])).
% 1.37/0.54  fof(f8,axiom,(
% 1.37/0.54    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.37/0.54  fof(f60,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f40])).
% 1.37/0.54  fof(f40,plain,(
% 1.37/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.37/0.54    inference(nnf_transformation,[],[f12])).
% 1.37/0.54  fof(f12,axiom,(
% 1.37/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.37/0.54  fof(f121,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X1,k6_subset_1(X1,X0)))) )),
% 1.37/0.54    inference(superposition,[],[f66,f65])).
% 1.37/0.54  fof(f65,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f52,f64,f64])).
% 1.37/0.54  fof(f52,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f1])).
% 1.37/0.54  fof(f1,axiom,(
% 1.37/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.37/0.54  fof(f66,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f54,f51,f64])).
% 1.37/0.54  fof(f54,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.37/0.54  fof(f175,plain,(
% 1.37/0.54    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(backward_demodulation,[],[f45,f169])).
% 1.37/0.54  fof(f45,plain,(
% 1.37/0.54    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(cnf_transformation,[],[f39])).
% 1.37/0.54  fof(f1660,plain,(
% 1.37/0.54    v4_pre_topc(sK1,sK0)),
% 1.37/0.54    inference(backward_demodulation,[],[f249,f1658])).
% 1.37/0.54  fof(f1658,plain,(
% 1.37/0.54    sK1 = k2_pre_topc(sK0,sK1)),
% 1.37/0.54    inference(duplicate_literal_removal,[],[f1657])).
% 1.37/0.54  fof(f1657,plain,(
% 1.37/0.54    sK1 = k2_pre_topc(sK0,sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.37/0.54    inference(superposition,[],[f1620,f1631])).
% 1.37/0.54  fof(f1631,plain,(
% 1.37/0.54    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.37/0.54    inference(superposition,[],[f800,f1622])).
% 1.37/0.54  fof(f1622,plain,(
% 1.37/0.54    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.37/0.54    inference(superposition,[],[f1620,f855])).
% 1.37/0.54  fof(f855,plain,(
% 1.37/0.54    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(forward_demodulation,[],[f853,f50])).
% 1.37/0.54  fof(f50,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f6])).
% 1.37/0.54  fof(f6,axiom,(
% 1.37/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.37/0.54  fof(f853,plain,(
% 1.37/0.54    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) | sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1))),
% 1.37/0.54    inference(resolution,[],[f790,f67])).
% 1.37/0.54  fof(f67,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1) )),
% 1.37/0.54    inference(definition_unfolding,[],[f56,f53])).
% 1.37/0.54  fof(f53,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f7])).
% 1.37/0.54  fof(f7,axiom,(
% 1.37/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.37/0.54  fof(f56,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f26])).
% 1.37/0.54  fof(f26,plain,(
% 1.37/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.37/0.54    inference(ennf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.37/0.54  fof(f790,plain,(
% 1.37/0.54    r1_tarski(k2_tops_1(sK0,sK1),sK1) | k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(backward_demodulation,[],[f414,f759])).
% 1.37/0.54  fof(f414,plain,(
% 1.37/0.54    r1_tarski(k2_tops_1(sK0,sK1),sK1) | k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(resolution,[],[f413,f176])).
% 1.37/0.54  fof(f176,plain,(
% 1.37/0.54    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(backward_demodulation,[],[f44,f169])).
% 1.37/0.54  fof(f44,plain,(
% 1.37/0.54    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(cnf_transformation,[],[f39])).
% 1.37/0.54  fof(f413,plain,(
% 1.37/0.54    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.37/0.54    inference(subsumption_resolution,[],[f405,f42])).
% 1.37/0.54  fof(f405,plain,(
% 1.37/0.54    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f48,f43])).
% 1.37/0.54  fof(f48,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f25])).
% 1.37/0.54  fof(f25,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(flattening,[],[f24])).
% 1.37/0.54  fof(f24,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f16])).
% 1.37/0.54  fof(f16,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 1.37/0.54  fof(f800,plain,(
% 1.37/0.54    sK1 = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK1,k1_tops_1(sK0,sK1))))),
% 1.37/0.54    inference(superposition,[],[f77,f759])).
% 1.37/0.54  fof(f77,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k6_subset_1(X0,X1))) = X0) )),
% 1.37/0.54    inference(forward_demodulation,[],[f76,f50])).
% 1.37/0.54  fof(f76,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(k6_subset_1(X0,X1),X0)) = X0) )),
% 1.37/0.54    inference(resolution,[],[f67,f72])).
% 1.37/0.54  fof(f1620,plain,(
% 1.37/0.54    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 1.37/0.54    inference(forward_demodulation,[],[f1614,f573])).
% 1.37/0.54  fof(f573,plain,(
% 1.37/0.54    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.37/0.54    inference(subsumption_resolution,[],[f563,f42])).
% 1.37/0.54  fof(f563,plain,(
% 1.37/0.54    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f46,f43])).
% 1.37/0.54  fof(f46,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f22])).
% 1.37/0.54  fof(f22,plain,(
% 1.37/0.54    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(ennf_transformation,[],[f15])).
% 1.37/0.54  fof(f15,axiom,(
% 1.37/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.37/0.54  fof(f1614,plain,(
% 1.37/0.54    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.37/0.54    inference(superposition,[],[f1586,f454])).
% 1.37/0.54  fof(f454,plain,(
% 1.37/0.54    k2_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 1.37/0.54    inference(backward_demodulation,[],[f419,f427])).
% 1.37/0.54  fof(f427,plain,(
% 1.37/0.54    k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k5_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),
% 1.37/0.54    inference(superposition,[],[f121,f335])).
% 1.37/0.54  fof(f335,plain,(
% 1.37/0.54    k2_tops_1(sK0,sK1) = k6_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_tops_1(sK0,sK1),u1_struct_0(sK0)))),
% 1.37/0.54    inference(resolution,[],[f331,f68])).
% 1.37/0.54  fof(f331,plain,(
% 1.37/0.54    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.37/0.54    inference(resolution,[],[f326,f60])).
% 1.37/0.54  fof(f326,plain,(
% 1.37/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.54    inference(subsumption_resolution,[],[f322,f42])).
% 1.37/0.54  fof(f322,plain,(
% 1.37/0.54    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f59,f43])).
% 1.37/0.54  fof(f59,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f31])).
% 1.37/0.54  fof(f31,plain,(
% 1.37/0.54    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.37/0.54    inference(flattening,[],[f30])).
% 1.37/0.54  fof(f30,plain,(
% 1.37/0.54    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f13])).
% 1.37/0.54  fof(f13,axiom,(
% 1.37/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.37/0.54  fof(f419,plain,(
% 1.37/0.54    k2_tops_1(sK0,sK1) = k6_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 1.37/0.54    inference(superposition,[],[f335,f65])).
% 1.37/0.54  fof(f1586,plain,(
% 1.37/0.54    ( ! [X52] : (k4_subset_1(u1_struct_0(sK0),sK1,k6_subset_1(u1_struct_0(sK0),X52)) = k3_tarski(k2_tarski(sK1,k6_subset_1(u1_struct_0(sK0),X52)))) )),
% 1.37/0.54    inference(resolution,[],[f507,f43])).
% 1.37/0.54  fof(f507,plain,(
% 1.37/0.54    ( ! [X6,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(X5)) | k4_subset_1(X5,X6,k6_subset_1(X5,X7)) = k3_tarski(k2_tarski(X6,k6_subset_1(X5,X7)))) )),
% 1.37/0.54    inference(resolution,[],[f70,f49])).
% 1.37/0.54  fof(f70,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f63,f53])).
% 1.37/0.54  fof(f63,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f34])).
% 1.37/0.54  fof(f34,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.37/0.54    inference(flattening,[],[f33])).
% 1.37/0.54  fof(f33,plain,(
% 1.37/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.37/0.54    inference(ennf_transformation,[],[f9])).
% 1.37/0.54  fof(f9,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.37/0.54  fof(f249,plain,(
% 1.37/0.54    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 1.37/0.54    inference(subsumption_resolution,[],[f248,f41])).
% 1.37/0.54  fof(f41,plain,(
% 1.37/0.54    v2_pre_topc(sK0)),
% 1.37/0.54    inference(cnf_transformation,[],[f39])).
% 1.37/0.54  fof(f248,plain,(
% 1.37/0.54    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~v2_pre_topc(sK0)),
% 1.37/0.54    inference(subsumption_resolution,[],[f245,f42])).
% 1.37/0.54  fof(f245,plain,(
% 1.37/0.54    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.37/0.54    inference(resolution,[],[f58,f43])).
% 1.37/0.54  fof(f58,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f29])).
% 1.37/0.54  fof(f29,plain,(
% 1.37/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.54    inference(flattening,[],[f28])).
% 1.37/0.54  fof(f28,plain,(
% 1.37/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.37/0.54    inference(ennf_transformation,[],[f14])).
% 1.37/0.54  fof(f14,axiom,(
% 1.37/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.37/0.54  fof(f1716,plain,(
% 1.37/0.54    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.37/0.54    inference(forward_demodulation,[],[f1697,f723])).
% 1.37/0.54  fof(f1697,plain,(
% 1.37/0.54    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k6_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 1.37/0.54    inference(superposition,[],[f117,f1666])).
% 1.37/0.54  fof(f1666,plain,(
% 1.37/0.54    k2_tops_1(sK0,sK1) = k6_subset_1(k2_tops_1(sK0,sK1),k6_subset_1(k2_tops_1(sK0,sK1),sK1))),
% 1.37/0.54    inference(resolution,[],[f1665,f68])).
% 1.37/0.54  fof(f1665,plain,(
% 1.37/0.54    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.37/0.54    inference(resolution,[],[f1660,f413])).
% 1.37/0.54  fof(f117,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k6_subset_1(X1,k6_subset_1(X1,X0)) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X1,k6_subset_1(X1,X0))))) )),
% 1.37/0.54    inference(superposition,[],[f66,f65])).
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (27332)------------------------------
% 1.37/0.54  % (27332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (27332)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (27332)Memory used [KB]: 2558
% 1.37/0.54  % (27332)Time elapsed: 0.060 s
% 1.37/0.54  % (27332)------------------------------
% 1.37/0.54  % (27332)------------------------------
% 1.37/0.54  % (27319)Success in time 0.179 s
%------------------------------------------------------------------------------
