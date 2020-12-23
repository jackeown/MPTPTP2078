%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:49 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 499 expanded)
%              Number of leaves         :   21 ( 136 expanded)
%              Depth                    :   21
%              Number of atoms          :  271 (2201 expanded)
%              Number of equality atoms :  106 ( 694 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1021,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1018,f887])).

fof(f887,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f883])).

fof(f883,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f86,f882])).

fof(f882,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f862])).

fof(f862,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f411,f226])).

fof(f226,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f142,f102])).

fof(f102,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f93,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f93,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f92,f43])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f92,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f91,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f52,f85])).

fof(f85,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f45,f84])).

fof(f84,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f65,f44])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f45,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f142,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f71,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f411,plain,(
    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f57,f179])).

fof(f179,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f105,f84])).

fof(f105,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f96,f44])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f51,f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f86,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f46,f84])).

fof(f46,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f1018,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f97,f1015])).

fof(f1015,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(backward_demodulation,[],[f446,f1010])).

fof(f1010,plain,(
    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f527,f884])).

fof(f884,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f411,f882])).

fof(f527,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f518,f193])).

fof(f193,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f186,f48])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f186,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f56,f120])).

fof(f120,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f81,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f64,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f518,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f56,f296])).

fof(f296,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f257,f57])).

fof(f257,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(backward_demodulation,[],[f148,f256])).

fof(f256,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f107,f252])).

fof(f252,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f249,f223])).

fof(f223,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f142,f73])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f59,f47])).

fof(f249,plain,(
    ! [X3] : k4_xboole_0(X3,X3) = k3_xboole_0(X3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f162,f223])).

fof(f162,plain,(
    ! [X3] : k4_xboole_0(X3,X3) = k3_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f155,f74])).

fof(f74,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f59,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f155,plain,(
    ! [X3] : k4_xboole_0(X3,k3_xboole_0(X3,X3)) = k3_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f78,f77])).

fof(f77,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f57,f49])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f78,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f57,f57])).

fof(f107,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f58,f74])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f148,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f58,f75])).

fof(f75,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f59,f53])).

fof(f446,plain,(
    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f443,f104])).

fof(f104,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f95,f44])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f50,f43])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f443,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f117,f44])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k2_xboole_0(X0,k2_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f100,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f100,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f90,f44])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f61,f43])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f97,plain,(
    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    inference(resolution,[],[f89,f44])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f88,f43])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ) ),
    inference(resolution,[],[f60,f42])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:46:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.55  % (20943)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (20935)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.56  % (20927)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.57  % (20936)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.57  % (20928)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.58  % (20944)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.58  % (20936)Refutation not found, incomplete strategy% (20936)------------------------------
% 0.20/0.58  % (20936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (20921)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.59  % (20920)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.59  % (20936)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (20936)Memory used [KB]: 10618
% 0.20/0.59  % (20936)Time elapsed: 0.145 s
% 0.20/0.59  % (20936)------------------------------
% 0.20/0.59  % (20936)------------------------------
% 0.20/0.59  % (20923)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.60  % (20922)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.60  % (20925)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.60  % (20926)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.60  % (20933)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.60  % (20932)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.61  % (20942)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.82/0.62  % (20931)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.82/0.62  % (20946)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.82/0.62  % (20941)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.82/0.62  % (20937)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.82/0.62  % (20924)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.82/0.62  % (20934)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.82/0.62  % (20947)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.82/0.62  % (20929)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.82/0.63  % (20938)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.82/0.63  % (20939)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.82/0.63  % (20945)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.07/0.63  % (20949)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.07/0.63  % (20949)Refutation not found, incomplete strategy% (20949)------------------------------
% 2.07/0.63  % (20949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (20949)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.63  
% 2.07/0.63  % (20949)Memory used [KB]: 1663
% 2.07/0.63  % (20949)Time elapsed: 0.003 s
% 2.07/0.63  % (20949)------------------------------
% 2.07/0.63  % (20949)------------------------------
% 2.07/0.64  % (20930)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.07/0.64  % (20948)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.07/0.64  % (20930)Refutation not found, incomplete strategy% (20930)------------------------------
% 2.07/0.64  % (20930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.64  % (20930)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.64  
% 2.07/0.64  % (20930)Memory used [KB]: 10746
% 2.07/0.64  % (20930)Time elapsed: 0.205 s
% 2.07/0.64  % (20930)------------------------------
% 2.07/0.64  % (20930)------------------------------
% 2.07/0.64  % (20948)Refutation not found, incomplete strategy% (20948)------------------------------
% 2.07/0.64  % (20948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.64  % (20948)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.64  
% 2.07/0.64  % (20948)Memory used [KB]: 10746
% 2.07/0.64  % (20948)Time elapsed: 0.204 s
% 2.07/0.64  % (20948)------------------------------
% 2.07/0.64  % (20948)------------------------------
% 2.07/0.64  % (20940)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.07/0.64  % (20927)Refutation found. Thanks to Tanya!
% 2.07/0.64  % SZS status Theorem for theBenchmark
% 2.07/0.64  % SZS output start Proof for theBenchmark
% 2.07/0.64  fof(f1021,plain,(
% 2.07/0.64    $false),
% 2.07/0.64    inference(subsumption_resolution,[],[f1018,f887])).
% 2.07/0.64  fof(f887,plain,(
% 2.07/0.64    ~v4_pre_topc(sK1,sK0)),
% 2.07/0.64    inference(trivial_inequality_removal,[],[f883])).
% 2.07/0.64  fof(f883,plain,(
% 2.07/0.64    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 2.07/0.64    inference(backward_demodulation,[],[f86,f882])).
% 2.07/0.64  fof(f882,plain,(
% 2.07/0.64    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.07/0.64    inference(duplicate_literal_removal,[],[f862])).
% 2.07/0.64  fof(f862,plain,(
% 2.07/0.64    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.07/0.64    inference(superposition,[],[f411,f226])).
% 2.22/0.65  fof(f226,plain,(
% 2.22/0.65    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.65    inference(superposition,[],[f142,f102])).
% 2.22/0.65  fof(f102,plain,(
% 2.22/0.65    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.65    inference(resolution,[],[f93,f59])).
% 2.22/0.65  fof(f59,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.22/0.65    inference(cnf_transformation,[],[f27])).
% 2.22/0.65  fof(f27,plain,(
% 2.22/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.22/0.65    inference(ennf_transformation,[],[f4])).
% 2.22/0.65  fof(f4,axiom,(
% 2.22/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.22/0.65  fof(f93,plain,(
% 2.22/0.65    r1_tarski(k2_tops_1(sK0,sK1),sK1) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.65    inference(subsumption_resolution,[],[f92,f43])).
% 2.22/0.65  fof(f43,plain,(
% 2.22/0.65    l1_pre_topc(sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f39])).
% 2.22/0.65  fof(f39,plain,(
% 2.22/0.65    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.22/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 2.22/0.65  fof(f37,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f38,plain,(
% 2.22/0.65    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.22/0.65    introduced(choice_axiom,[])).
% 2.22/0.65  fof(f36,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.22/0.65    inference(flattening,[],[f35])).
% 2.22/0.65  fof(f35,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.22/0.65    inference(nnf_transformation,[],[f22])).
% 2.22/0.65  fof(f22,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.22/0.65    inference(flattening,[],[f21])).
% 2.22/0.65  fof(f21,plain,(
% 2.22/0.65    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f20])).
% 2.22/0.65  fof(f20,negated_conjecture,(
% 2.22/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.22/0.65    inference(negated_conjecture,[],[f19])).
% 2.22/0.65  fof(f19,conjecture,(
% 2.22/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 2.22/0.65  fof(f92,plain,(
% 2.22/0.65    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.65    inference(subsumption_resolution,[],[f91,f44])).
% 2.22/0.65  fof(f44,plain,(
% 2.22/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.65    inference(cnf_transformation,[],[f39])).
% 2.22/0.65  fof(f91,plain,(
% 2.22/0.65    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.65    inference(resolution,[],[f52,f85])).
% 2.22/0.65  fof(f85,plain,(
% 2.22/0.65    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.65    inference(backward_demodulation,[],[f45,f84])).
% 2.22/0.65  fof(f84,plain,(
% 2.22/0.65    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 2.22/0.65    inference(resolution,[],[f65,f44])).
% 2.22/0.65  fof(f65,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f32])).
% 2.22/0.65  fof(f32,plain,(
% 2.22/0.65    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f12])).
% 2.22/0.65  fof(f12,axiom,(
% 2.22/0.65    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.22/0.65  fof(f45,plain,(
% 2.22/0.65    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.65    inference(cnf_transformation,[],[f39])).
% 2.22/0.65  fof(f52,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f26])).
% 2.22/0.65  fof(f26,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(flattening,[],[f25])).
% 2.22/0.65  fof(f25,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f17])).
% 2.22/0.65  fof(f17,axiom,(
% 2.22/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 2.22/0.65  fof(f142,plain,(
% 2.22/0.65    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 2.22/0.65    inference(superposition,[],[f71,f55])).
% 2.22/0.65  fof(f55,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f13])).
% 2.22/0.65  fof(f13,axiom,(
% 2.22/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.22/0.65  fof(f71,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 2.22/0.65    inference(superposition,[],[f55,f54])).
% 2.22/0.65  fof(f54,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f10])).
% 2.22/0.65  fof(f10,axiom,(
% 2.22/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.22/0.65  fof(f411,plain,(
% 2.22/0.65    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.22/0.65    inference(superposition,[],[f57,f179])).
% 2.22/0.65  fof(f179,plain,(
% 2.22/0.65    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.22/0.65    inference(superposition,[],[f105,f84])).
% 2.22/0.65  fof(f105,plain,(
% 2.22/0.65    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.22/0.65    inference(resolution,[],[f96,f44])).
% 2.22/0.65  fof(f96,plain,(
% 2.22/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 2.22/0.65    inference(resolution,[],[f51,f43])).
% 2.22/0.65  fof(f51,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f24])).
% 2.22/0.65  fof(f24,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f18])).
% 2.22/0.65  fof(f18,axiom,(
% 2.22/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.22/0.65  fof(f57,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f8])).
% 2.22/0.65  fof(f8,axiom,(
% 2.22/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.22/0.65  fof(f86,plain,(
% 2.22/0.65    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.65    inference(backward_demodulation,[],[f46,f84])).
% 2.22/0.65  fof(f46,plain,(
% 2.22/0.65    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.22/0.65    inference(cnf_transformation,[],[f39])).
% 2.22/0.65  fof(f1018,plain,(
% 2.22/0.65    v4_pre_topc(sK1,sK0)),
% 2.22/0.65    inference(backward_demodulation,[],[f97,f1015])).
% 2.22/0.65  fof(f1015,plain,(
% 2.22/0.65    sK1 = k2_pre_topc(sK0,sK1)),
% 2.22/0.65    inference(backward_demodulation,[],[f446,f1010])).
% 2.22/0.65  fof(f1010,plain,(
% 2.22/0.65    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.22/0.65    inference(superposition,[],[f527,f884])).
% 2.22/0.65  fof(f884,plain,(
% 2.22/0.65    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.22/0.65    inference(backward_demodulation,[],[f411,f882])).
% 2.22/0.65  fof(f527,plain,(
% 2.22/0.65    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2) )),
% 2.22/0.65    inference(forward_demodulation,[],[f518,f193])).
% 2.22/0.65  fof(f193,plain,(
% 2.22/0.65    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.22/0.65    inference(forward_demodulation,[],[f186,f48])).
% 2.22/0.65  fof(f48,plain,(
% 2.22/0.65    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.22/0.65    inference(cnf_transformation,[],[f3])).
% 2.22/0.65  fof(f3,axiom,(
% 2.22/0.65    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.22/0.65  fof(f186,plain,(
% 2.22/0.65    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X1,k1_xboole_0)) )),
% 2.22/0.65    inference(superposition,[],[f56,f120])).
% 2.22/0.65  fof(f120,plain,(
% 2.22/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.22/0.65    inference(resolution,[],[f81,f53])).
% 2.22/0.65  fof(f53,plain,(
% 2.22/0.65    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f6])).
% 2.22/0.65  fof(f6,axiom,(
% 2.22/0.65    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.22/0.65  fof(f81,plain,(
% 2.22/0.65    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.22/0.65    inference(resolution,[],[f64,f47])).
% 2.22/0.65  fof(f47,plain,(
% 2.22/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f5])).
% 2.22/0.65  fof(f5,axiom,(
% 2.22/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.22/0.65  fof(f64,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f41])).
% 2.22/0.65  fof(f41,plain,(
% 2.22/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.65    inference(flattening,[],[f40])).
% 2.22/0.65  fof(f40,plain,(
% 2.22/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.22/0.65    inference(nnf_transformation,[],[f1])).
% 2.22/0.65  fof(f1,axiom,(
% 2.22/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.22/0.65  fof(f56,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f9])).
% 2.22/0.65  fof(f9,axiom,(
% 2.22/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.22/0.65  fof(f518,plain,(
% 2.22/0.65    ( ! [X2,X3] : (k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 2.22/0.65    inference(superposition,[],[f56,f296])).
% 2.22/0.65  fof(f296,plain,(
% 2.22/0.65    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 2.22/0.65    inference(superposition,[],[f257,f57])).
% 2.22/0.65  fof(f257,plain,(
% 2.22/0.65    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 2.22/0.65    inference(backward_demodulation,[],[f148,f256])).
% 2.22/0.65  fof(f256,plain,(
% 2.22/0.65    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.22/0.65    inference(backward_demodulation,[],[f107,f252])).
% 2.22/0.65  fof(f252,plain,(
% 2.22/0.65    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 2.22/0.65    inference(forward_demodulation,[],[f249,f223])).
% 2.22/0.65  fof(f223,plain,(
% 2.22/0.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.22/0.65    inference(superposition,[],[f142,f73])).
% 2.22/0.65  fof(f73,plain,(
% 2.22/0.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.22/0.65    inference(resolution,[],[f59,f47])).
% 2.22/0.65  fof(f249,plain,(
% 2.22/0.65    ( ! [X3] : (k4_xboole_0(X3,X3) = k3_xboole_0(X3,k1_xboole_0)) )),
% 2.22/0.65    inference(backward_demodulation,[],[f162,f223])).
% 2.22/0.65  fof(f162,plain,(
% 2.22/0.65    ( ! [X3] : (k4_xboole_0(X3,X3) = k3_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) )),
% 2.22/0.65    inference(forward_demodulation,[],[f155,f74])).
% 2.22/0.65  fof(f74,plain,(
% 2.22/0.65    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 2.22/0.65    inference(resolution,[],[f59,f67])).
% 2.22/0.65  fof(f67,plain,(
% 2.22/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.22/0.65    inference(equality_resolution,[],[f63])).
% 2.22/0.65  fof(f63,plain,(
% 2.22/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.22/0.65    inference(cnf_transformation,[],[f41])).
% 2.22/0.65  fof(f155,plain,(
% 2.22/0.65    ( ! [X3] : (k4_xboole_0(X3,k3_xboole_0(X3,X3)) = k3_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) )),
% 2.22/0.65    inference(superposition,[],[f78,f77])).
% 2.22/0.65  fof(f77,plain,(
% 2.22/0.65    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 2.22/0.65    inference(superposition,[],[f57,f49])).
% 2.22/0.65  fof(f49,plain,(
% 2.22/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.22/0.65    inference(cnf_transformation,[],[f7])).
% 2.22/0.65  fof(f7,axiom,(
% 2.22/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.22/0.65  fof(f78,plain,(
% 2.22/0.65    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 2.22/0.65    inference(superposition,[],[f57,f57])).
% 2.22/0.65  fof(f107,plain,(
% 2.22/0.65    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 2.22/0.65    inference(superposition,[],[f58,f74])).
% 2.22/0.65  fof(f58,plain,(
% 2.22/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f2])).
% 2.22/0.65  fof(f2,axiom,(
% 2.22/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.22/0.65  fof(f148,plain,(
% 2.22/0.65    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 2.22/0.65    inference(superposition,[],[f58,f75])).
% 2.22/0.65  fof(f75,plain,(
% 2.22/0.65    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 2.22/0.65    inference(resolution,[],[f59,f53])).
% 2.22/0.65  fof(f446,plain,(
% 2.22/0.65    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.22/0.65    inference(forward_demodulation,[],[f443,f104])).
% 2.22/0.65  fof(f104,plain,(
% 2.22/0.65    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.22/0.65    inference(resolution,[],[f95,f44])).
% 2.22/0.65  fof(f95,plain,(
% 2.22/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 2.22/0.65    inference(resolution,[],[f50,f43])).
% 2.22/0.65  fof(f50,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f23])).
% 2.22/0.65  fof(f23,plain,(
% 2.22/0.65    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(ennf_transformation,[],[f16])).
% 2.22/0.65  fof(f16,axiom,(
% 2.22/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.22/0.65  fof(f443,plain,(
% 2.22/0.65    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.22/0.65    inference(resolution,[],[f117,f44])).
% 2.22/0.65  fof(f117,plain,(
% 2.22/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k2_xboole_0(X0,k2_tops_1(sK0,sK1))) )),
% 2.22/0.65    inference(resolution,[],[f100,f66])).
% 2.22/0.65  fof(f66,plain,(
% 2.22/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f34])).
% 2.22/0.65  fof(f34,plain,(
% 2.22/0.65    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.22/0.65    inference(flattening,[],[f33])).
% 2.22/0.65  fof(f33,plain,(
% 2.22/0.65    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.22/0.65    inference(ennf_transformation,[],[f11])).
% 2.22/0.65  fof(f11,axiom,(
% 2.22/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.22/0.65  fof(f100,plain,(
% 2.22/0.65    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.22/0.65    inference(resolution,[],[f90,f44])).
% 2.22/0.65  fof(f90,plain,(
% 2.22/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.22/0.65    inference(resolution,[],[f61,f43])).
% 2.22/0.65  fof(f61,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.22/0.65    inference(cnf_transformation,[],[f31])).
% 2.22/0.65  fof(f31,plain,(
% 2.22/0.65    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.22/0.65    inference(flattening,[],[f30])).
% 2.22/0.65  fof(f30,plain,(
% 2.22/0.65    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f14])).
% 2.22/0.65  fof(f14,axiom,(
% 2.22/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.22/0.65  fof(f97,plain,(
% 2.22/0.65    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 2.22/0.65    inference(resolution,[],[f89,f44])).
% 2.22/0.65  fof(f89,plain,(
% 2.22/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k2_pre_topc(sK0,X0),sK0)) )),
% 2.22/0.65    inference(subsumption_resolution,[],[f88,f43])).
% 2.22/0.65  fof(f88,plain,(
% 2.22/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(k2_pre_topc(sK0,X0),sK0)) )),
% 2.22/0.65    inference(resolution,[],[f60,f42])).
% 2.22/0.65  fof(f42,plain,(
% 2.22/0.65    v2_pre_topc(sK0)),
% 2.22/0.65    inference(cnf_transformation,[],[f39])).
% 2.22/0.65  fof(f60,plain,(
% 2.22/0.65    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 2.22/0.65    inference(cnf_transformation,[],[f29])).
% 2.22/0.65  fof(f29,plain,(
% 2.22/0.65    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.22/0.65    inference(flattening,[],[f28])).
% 2.22/0.65  fof(f28,plain,(
% 2.22/0.65    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.22/0.65    inference(ennf_transformation,[],[f15])).
% 2.22/0.65  fof(f15,axiom,(
% 2.22/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 2.22/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 2.22/0.65  % SZS output end Proof for theBenchmark
% 2.22/0.65  % (20927)------------------------------
% 2.22/0.65  % (20927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.65  % (20927)Termination reason: Refutation
% 2.22/0.65  
% 2.22/0.65  % (20927)Memory used [KB]: 2174
% 2.22/0.65  % (20927)Time elapsed: 0.158 s
% 2.22/0.65  % (20927)------------------------------
% 2.22/0.65  % (20927)------------------------------
% 2.22/0.66  % (20919)Success in time 0.288 s
%------------------------------------------------------------------------------
