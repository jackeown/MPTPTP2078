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
% DateTime   : Thu Dec  3 13:10:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 (1271 expanded)
%              Number of leaves         :   13 ( 357 expanded)
%              Depth                    :   20
%              Number of atoms          :  191 (5145 expanded)
%              Number of equality atoms :   31 ( 294 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(subsumption_resolution,[],[f243,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f30,f47])).

fof(f47,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f34,f45])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v4_pre_topc(X1,sK0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | ~ v4_pre_topc(X1,sK0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v4_pre_topc(sK1,sK0) )
      & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f243,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f242,f240])).

fof(f240,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f239,f79])).

fof(f79,plain,
    ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f50,f66])).

fof(f66,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f40,f48])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f50,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f32,f47])).

fof(f32,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f239,plain,(
    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f238,f78])).

fof(f78,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f49,f66])).

fof(f49,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f31,f47])).

fof(f31,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f238,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f219,f237])).

fof(f237,plain,(
    k4_xboole_0(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f234,f211])).

fof(f211,plain,(
    k4_xboole_0(k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[],[f205,f164])).

fof(f164,plain,(
    sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f92,f163])).

fof(f163,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f159,f66])).

fof(f159,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f41,f48])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f92,plain,(
    k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f68,f66])).

fof(f68,plain,(
    k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f40,f54])).

fof(f54,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f39,f48])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f205,plain,(
    ! [X2] : k9_subset_1(k2_struct_0(sK0),X2,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f44,f80])).

fof(f80,plain,(
    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f54,f66])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f234,plain,(
    k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f229,f53])).

fof(f53,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f52,f47])).

fof(f52,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f35,f45])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f229,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),X0,sK1) ) ),
    inference(forward_demodulation,[],[f225,f66])).

fof(f225,plain,(
    ! [X0] :
      ( k7_subset_1(k2_struct_0(sK0),X0,sK1) = k9_subset_1(k2_struct_0(sK0),X0,k3_subset_1(k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f42,f48])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f219,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f218,f48])).

fof(f218,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f217,f29])).

fof(f217,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f36,f47])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f242,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f241,f239])).

fof(f241,plain,
    ( ~ v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f224,f237])).

fof(f224,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f223,f29])).

fof(f223,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f37,f47])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:58:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (29851)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (29850)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (29845)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (29841)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (29853)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (29846)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (29840)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (29853)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f243,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f30,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f34,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f33,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.50    inference(negated_conjecture,[],[f11])).
% 0.21/0.50  fof(f11,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f242,f240])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f239,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f50,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 0.21/0.50    inference(resolution,[],[f40,f48])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f32,f47])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f238,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f49,f66])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f31,f47])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f219,f237])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    k4_xboole_0(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.21/0.50    inference(forward_demodulation,[],[f234,f211])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    k4_xboole_0(k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.50    inference(superposition,[],[f205,f164])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.50    inference(backward_demodulation,[],[f92,f163])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.50    inference(forward_demodulation,[],[f159,f66])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.21/0.50    inference(resolution,[],[f41,f48])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.50    inference(forward_demodulation,[],[f68,f66])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.21/0.50    inference(resolution,[],[f40,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(resolution,[],[f39,f48])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ( ! [X2] : (k9_subset_1(k2_struct_0(sK0),X2,k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k2_struct_0(sK0),sK1)))) )),
% 0.21/0.50    inference(resolution,[],[f44,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f54,f66])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f43,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.21/0.50    inference(resolution,[],[f229,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(forward_demodulation,[],[f52,f47])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(resolution,[],[f35,f45])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),X0,sK1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f225,f66])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    ( ! [X0] : (k7_subset_1(k2_struct_0(sK0),X0,sK1) = k9_subset_1(k2_struct_0(sK0),X0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.50    inference(resolution,[],[f42,f48])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ~v4_pre_topc(sK1,sK0) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.50    inference(resolution,[],[f218,f48])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f217,f29])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.50    inference(superposition,[],[f36,f47])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f241,f239])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    ~v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(superposition,[],[f224,f237])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f223,f29])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.50    inference(superposition,[],[f37,f47])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (29853)------------------------------
% 0.21/0.50  % (29853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29853)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (29853)Memory used [KB]: 1791
% 0.21/0.50  % (29853)Time elapsed: 0.016 s
% 0.21/0.50  % (29853)------------------------------
% 0.21/0.50  % (29853)------------------------------
% 0.21/0.50  % (29839)Success in time 0.14 s
%------------------------------------------------------------------------------
