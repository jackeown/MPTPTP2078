%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:42 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 364 expanded)
%              Number of leaves         :   15 (  96 expanded)
%              Depth                    :   20
%              Number of atoms          :  281 (2020 expanded)
%              Number of equality atoms :   71 ( 532 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(subsumption_resolution,[],[f146,f115])).

fof(f115,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f114,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != X1
          | ~ v3_tops_1(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = X1
          | v3_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( sK1 != k2_tops_1(sK0,sK1)
        | ~ v3_tops_1(sK1,sK0) )
      & ( sK1 = k2_tops_1(sK0,sK1)
        | v3_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f114,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f113,f111])).

fof(f111,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f110,f93])).

fof(f93,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f92,f39])).

fof(f92,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f47,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

% (7361)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(f110,plain,
    ( v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f109,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f109,plain,
    ( ~ r1_tarski(sK1,sK1)
    | v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0) ),
    inference(superposition,[],[f107,f42])).

fof(f42,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f106,f39])).

fof(f106,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f113,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f112,f41])).

fof(f41,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f112,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f40])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | v3_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

fof(f146,plain,(
    ~ v3_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( sK1 != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f43,f139])).

fof(f139,plain,(
    sK1 = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f138,f40])).

fof(f138,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f137,f96])).

fof(f96,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f95,f39])).

fof(f95,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f94,f41])).

fof(f94,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f137,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f136,f96])).

fof(f136,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f135,f90])).

fof(f90,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f84,f80])).

fof(f80,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f77,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f77,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f67,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f84,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f80,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f135,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f134,f111])).

fof(f134,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f133,f39])).

fof(f133,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f128,f40])).

fof(f128,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(superposition,[],[f119,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f97,f39])).

fof(f97,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f119,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) = k2_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f45,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f43,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:33:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.21/0.52  % (7368)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.21/0.52  % (7371)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.21/0.52  % (7369)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.21/0.52  % (7371)Refutation not found, incomplete strategy% (7371)------------------------------
% 1.21/0.52  % (7371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (7368)Refutation not found, incomplete strategy% (7368)------------------------------
% 1.21/0.52  % (7368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (7371)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  % (7368)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (7371)Memory used [KB]: 6268
% 1.21/0.52  
% 1.21/0.52  % (7368)Memory used [KB]: 10746
% 1.21/0.52  % (7371)Time elapsed: 0.060 s
% 1.21/0.52  % (7368)Time elapsed: 0.060 s
% 1.21/0.52  % (7371)------------------------------
% 1.21/0.52  % (7371)------------------------------
% 1.21/0.52  % (7368)------------------------------
% 1.21/0.52  % (7368)------------------------------
% 1.21/0.53  % (7369)Refutation not found, incomplete strategy% (7369)------------------------------
% 1.21/0.53  % (7369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (7369)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (7369)Memory used [KB]: 6268
% 1.21/0.53  % (7369)Time elapsed: 0.063 s
% 1.21/0.53  % (7369)------------------------------
% 1.21/0.53  % (7369)------------------------------
% 1.21/0.53  % (7360)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.21/0.53  % (7346)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.21/0.53  % (7344)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.21/0.53  % (7344)Refutation not found, incomplete strategy% (7344)------------------------------
% 1.21/0.53  % (7344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (7344)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (7344)Memory used [KB]: 1663
% 1.21/0.53  % (7344)Time elapsed: 0.112 s
% 1.21/0.53  % (7344)------------------------------
% 1.21/0.53  % (7344)------------------------------
% 1.38/0.54  % (7347)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.38/0.54  % (7350)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.54  % (7345)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.38/0.54  % (7352)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.54  % (7358)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.54  % (7364)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.54  % (7352)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % SZS output start Proof for theBenchmark
% 1.38/0.54  fof(f147,plain,(
% 1.38/0.54    $false),
% 1.38/0.54    inference(subsumption_resolution,[],[f146,f115])).
% 1.38/0.54  fof(f115,plain,(
% 1.38/0.54    v3_tops_1(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f114,f39])).
% 1.38/0.54  fof(f39,plain,(
% 1.38/0.54    l1_pre_topc(sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f34])).
% 1.38/0.54  fof(f34,plain,(
% 1.38/0.54    ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 1.38/0.54  fof(f32,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f33,plain,(
% 1.38/0.54    ? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f31,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f30])).
% 1.38/0.54  fof(f30,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f19])).
% 1.38/0.54  fof(f19,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f18])).
% 1.38/0.54  fof(f18,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f16])).
% 1.38/0.54  fof(f16,negated_conjecture,(
% 1.38/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.38/0.54    inference(negated_conjecture,[],[f15])).
% 1.38/0.54  fof(f15,conjecture,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).
% 1.38/0.54  fof(f114,plain,(
% 1.38/0.54    v3_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f113,f111])).
% 1.38/0.54  fof(f111,plain,(
% 1.38/0.54    v2_tops_1(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f110,f93])).
% 1.38/0.54  fof(f93,plain,(
% 1.38/0.54    ~v3_tops_1(sK1,sK0) | v2_tops_1(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f92,f39])).
% 1.38/0.54  fof(f92,plain,(
% 1.38/0.54    ~v3_tops_1(sK1,sK0) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.38/0.54    inference(resolution,[],[f47,f40])).
% 1.38/0.54  fof(f40,plain,(
% 1.38/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    inference(cnf_transformation,[],[f34])).
% 1.38/0.54  fof(f47,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f24])).
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f23])).
% 1.38/0.54  fof(f23,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f13])).
% 1.38/0.54  % (7361)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.54  fof(f13,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).
% 1.38/0.54  fof(f110,plain,(
% 1.38/0.54    v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f109,f62])).
% 1.38/0.54  fof(f62,plain,(
% 1.38/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.38/0.54    inference(equality_resolution,[],[f59])).
% 1.38/0.54  fof(f59,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.38/0.54    inference(cnf_transformation,[],[f38])).
% 1.38/0.54  fof(f38,plain,(
% 1.38/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.54    inference(flattening,[],[f37])).
% 1.38/0.54  fof(f37,plain,(
% 1.38/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.54    inference(nnf_transformation,[],[f1])).
% 1.38/0.54  fof(f1,axiom,(
% 1.38/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.54  fof(f109,plain,(
% 1.38/0.54    ~r1_tarski(sK1,sK1) | v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0)),
% 1.38/0.54    inference(superposition,[],[f107,f42])).
% 1.38/0.54  fof(f42,plain,(
% 1.38/0.54    sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f34])).
% 1.38/0.54  fof(f107,plain,(
% 1.38/0.54    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f106,f39])).
% 1.38/0.54  fof(f106,plain,(
% 1.38/0.54    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.38/0.54    inference(resolution,[],[f52,f40])).
% 1.38/0.54  fof(f52,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f36])).
% 1.38/0.54  fof(f36,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f12])).
% 1.38/0.54  fof(f12,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 1.38/0.54  fof(f113,plain,(
% 1.38/0.54    ~v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f112,f41])).
% 1.38/0.54  fof(f41,plain,(
% 1.38/0.54    v4_pre_topc(sK1,sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f34])).
% 1.38/0.54  fof(f112,plain,(
% 1.38/0.54    ~v4_pre_topc(sK1,sK0) | ~v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.38/0.54    inference(resolution,[],[f48,f40])).
% 1.38/0.54  fof(f48,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | v3_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f26])).
% 1.38/0.54  fof(f26,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f25])).
% 1.38/0.54  fof(f25,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f14])).
% 1.38/0.54  fof(f14,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).
% 1.38/0.54  fof(f146,plain,(
% 1.38/0.54    ~v3_tops_1(sK1,sK0)),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f140])).
% 1.38/0.54  fof(f140,plain,(
% 1.38/0.54    sK1 != sK1 | ~v3_tops_1(sK1,sK0)),
% 1.38/0.54    inference(backward_demodulation,[],[f43,f139])).
% 1.38/0.54  fof(f139,plain,(
% 1.38/0.54    sK1 = k2_tops_1(sK0,sK1)),
% 1.38/0.54    inference(subsumption_resolution,[],[f138,f40])).
% 1.38/0.54  fof(f138,plain,(
% 1.38/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_tops_1(sK0,sK1)),
% 1.38/0.54    inference(forward_demodulation,[],[f137,f96])).
% 1.38/0.54  fof(f96,plain,(
% 1.38/0.54    sK1 = k2_pre_topc(sK0,sK1)),
% 1.38/0.54    inference(subsumption_resolution,[],[f95,f39])).
% 1.38/0.54  fof(f95,plain,(
% 1.38/0.54    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f94,f41])).
% 1.38/0.54  fof(f94,plain,(
% 1.38/0.54    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.38/0.54    inference(resolution,[],[f46,f40])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f22])).
% 1.38/0.54  fof(f22,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f21])).
% 1.38/0.54  fof(f21,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f17])).
% 1.38/0.54  fof(f17,plain,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 1.38/0.54    inference(pure_predicate_removal,[],[f9])).
% 1.38/0.54  fof(f9,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.38/0.54  fof(f137,plain,(
% 1.38/0.54    sK1 = k2_tops_1(sK0,sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    inference(forward_demodulation,[],[f136,f96])).
% 1.38/0.54  fof(f136,plain,(
% 1.38/0.54    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    inference(forward_demodulation,[],[f135,f90])).
% 1.38/0.54  fof(f90,plain,(
% 1.38/0.54    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.38/0.54    inference(forward_demodulation,[],[f84,f80])).
% 1.38/0.54  fof(f80,plain,(
% 1.38/0.54    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.38/0.54    inference(superposition,[],[f77,f44])).
% 1.38/0.54  fof(f44,plain,(
% 1.38/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f3])).
% 1.38/0.54  fof(f3,axiom,(
% 1.38/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.38/0.54  fof(f77,plain,(
% 1.38/0.54    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.38/0.54    inference(superposition,[],[f67,f55])).
% 1.38/0.54  fof(f55,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f6])).
% 1.38/0.54  fof(f6,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.38/0.54  fof(f67,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.38/0.54    inference(superposition,[],[f55,f53])).
% 1.38/0.54  fof(f53,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f5])).
% 1.38/0.54  fof(f5,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.38/0.54  fof(f84,plain,(
% 1.38/0.54    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X1)) )),
% 1.38/0.54    inference(superposition,[],[f80,f57])).
% 1.38/0.54  fof(f57,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f4])).
% 1.38/0.54  fof(f4,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.38/0.54  fof(f135,plain,(
% 1.38/0.54    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    inference(subsumption_resolution,[],[f134,f111])).
% 1.38/0.54  fof(f134,plain,(
% 1.38/0.54    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f133,f39])).
% 1.38/0.54  fof(f133,plain,(
% 1.38/0.54    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f128,f40])).
% 1.38/0.54  fof(f128,plain,(
% 1.38/0.54    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 1.38/0.54    inference(superposition,[],[f119,f98])).
% 1.38/0.54  fof(f98,plain,(
% 1.38/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 1.38/0.54    inference(subsumption_resolution,[],[f97,f39])).
% 1.38/0.54  fof(f97,plain,(
% 1.38/0.54    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.38/0.54    inference(resolution,[],[f49,f40])).
% 1.38/0.54  fof(f49,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f35])).
% 1.38/0.54  fof(f35,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f27])).
% 1.38/0.54  fof(f27,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f11])).
% 1.38/0.54  fof(f11,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.38/0.54  fof(f119,plain,(
% 1.38/0.54    ( ! [X2,X3] : (k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) = k2_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.38/0.54    inference(superposition,[],[f45,f61])).
% 1.38/0.54  fof(f61,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f29])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f7])).
% 1.38/0.54  fof(f7,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.38/0.54  fof(f45,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f20])).
% 1.38/0.54  fof(f20,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f10])).
% 1.38/0.54  fof(f10,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.38/0.54  fof(f43,plain,(
% 1.38/0.54    sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f34])).
% 1.38/0.54  % SZS output end Proof for theBenchmark
% 1.38/0.54  % (7352)------------------------------
% 1.38/0.54  % (7352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (7352)Termination reason: Refutation
% 1.38/0.54  
% 1.38/0.54  % (7352)Memory used [KB]: 1791
% 1.38/0.54  % (7352)Time elapsed: 0.131 s
% 1.38/0.54  % (7352)------------------------------
% 1.38/0.54  % (7352)------------------------------
% 1.38/0.54  % (7366)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.55  % (7342)Success in time 0.181 s
%------------------------------------------------------------------------------
