%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:42 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  129 (1372 expanded)
%              Number of leaves         :   20 ( 363 expanded)
%              Depth                    :   32
%              Number of atoms          :  370 (6463 expanded)
%              Number of equality atoms :   99 (1752 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f807,plain,(
    $false ),
    inference(subsumption_resolution,[],[f806,f112])).

fof(f112,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f65,f111])).

fof(f111,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f73,f110])).

fof(f110,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f75,f64])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).

fof(f51,plain,
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

fof(f52,plain,
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

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f806,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f805,f111])).

fof(f805,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f804,f64])).

fof(f804,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f803,f793])).

fof(f793,plain,(
    ~ v3_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f791])).

fof(f791,plain,
    ( sK1 != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f68,f790])).

fof(f790,plain,(
    sK1 = k2_tops_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f789])).

fof(f789,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f788,f71])).

fof(f71,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f788,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f786,f134])).

fof(f134,plain,(
    ! [X4] : k7_subset_1(k2_struct_0(sK0),sK1,X4) = k4_xboole_0(sK1,X4) ),
    inference(resolution,[],[f95,f112])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f786,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(k2_struct_0(sK0),sK1,k1_xboole_0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f741,f776])).

fof(f776,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(backward_demodulation,[],[f191,f766])).

fof(f766,plain,(
    sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f174,f112])).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),X0)) = X0 ) ),
    inference(forward_demodulation,[],[f173,f132])).

fof(f132,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(resolution,[],[f95,f108])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f72,f69])).

fof(f69,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f173,plain,(
    ! [X0] :
      ( k4_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f172,f132])).

fof(f172,plain,(
    ! [X0] :
      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f171,f111])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ) ),
    inference(forward_demodulation,[],[f170,f111])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ) ),
    inference(resolution,[],[f74,f110])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

fof(f191,plain,(
    k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f190,f131])).

fof(f131,plain,(
    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f118,f127])).

fof(f127,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f90,f112])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f118,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f89,f112])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f190,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f189,f111])).

fof(f189,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f188,f132])).

fof(f188,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f187,f111])).

fof(f187,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f186,f64])).

fof(f186,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f77,f166])).

fof(f166,plain,(
    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f165,f112])).

fof(f165,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f164,f111])).

fof(f164,plain,
    ( v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f163,f132])).

fof(f163,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f162,f111])).

fof(f162,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f161,f64])).

fof(f161,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f80,f66])).

fof(f66,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).

fof(f741,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(superposition,[],[f222,f210])).

fof(f210,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f209,f112])).

fof(f209,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k2_tops_1(sK0,sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f208,f111])).

fof(f208,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f204,f64])).

fof(f204,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f138,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f138,plain,
    ( v2_tops_1(sK1,sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f137,f112])).

fof(f137,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_tops_1(sK1,sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f136,f111])).

fof(f136,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f135,f64])).

fof(f135,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(resolution,[],[f78,f67])).

fof(f67,plain,
    ( v3_tops_1(sK1,sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(f222,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f177,f112])).

fof(f177,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f176,f111])).

fof(f176,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f175,f111])).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f76,f64])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f68,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | sK1 != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f803,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f800,f66])).

fof(f800,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f794,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

fof(f794,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f792,f103])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f792,plain,
    ( ~ r1_tarski(sK1,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f218,f790])).

fof(f218,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f142,f112])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,k2_tops_1(sK0,X0))
      | v2_tops_1(X0,sK0) ) ),
    inference(forward_demodulation,[],[f141,f111])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f85,f64])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (22241)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (22233)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (22225)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (22221)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (22223)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (22222)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (22224)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (22220)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (22219)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (22218)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (22240)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (22226)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (22227)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (22245)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (22244)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (22246)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (22239)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (22237)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (22238)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (22242)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (22243)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (22219)Refutation not found, incomplete strategy% (22219)------------------------------
% 0.20/0.55  % (22219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22219)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22219)Memory used [KB]: 1663
% 0.20/0.55  % (22219)Time elapsed: 0.144 s
% 0.20/0.55  % (22219)------------------------------
% 0.20/0.55  % (22219)------------------------------
% 0.20/0.55  % (22230)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (22223)Refutation not found, incomplete strategy% (22223)------------------------------
% 0.20/0.55  % (22223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22223)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22223)Memory used [KB]: 1791
% 0.20/0.55  % (22223)Time elapsed: 0.126 s
% 0.20/0.55  % (22223)------------------------------
% 0.20/0.55  % (22223)------------------------------
% 0.20/0.55  % (22230)Refutation not found, incomplete strategy% (22230)------------------------------
% 0.20/0.55  % (22230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22230)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22230)Memory used [KB]: 10618
% 0.20/0.55  % (22230)Time elapsed: 0.146 s
% 0.20/0.55  % (22230)------------------------------
% 0.20/0.55  % (22230)------------------------------
% 0.20/0.55  % (22234)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (22231)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (22232)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.56  % (22234)Refutation not found, incomplete strategy% (22234)------------------------------
% 0.20/0.56  % (22234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (22234)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (22234)Memory used [KB]: 10746
% 0.20/0.56  % (22234)Time elapsed: 0.156 s
% 0.20/0.56  % (22234)------------------------------
% 0.20/0.56  % (22234)------------------------------
% 0.20/0.56  % (22232)Refutation not found, incomplete strategy% (22232)------------------------------
% 0.20/0.56  % (22232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (22232)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (22232)Memory used [KB]: 1791
% 0.20/0.56  % (22232)Time elapsed: 0.158 s
% 0.20/0.56  % (22232)------------------------------
% 0.20/0.56  % (22232)------------------------------
% 0.20/0.56  % (22247)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (22235)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.56  % (22245)Refutation not found, incomplete strategy% (22245)------------------------------
% 0.20/0.56  % (22245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (22245)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (22245)Memory used [KB]: 6268
% 0.20/0.56  % (22245)Time elapsed: 0.137 s
% 0.20/0.56  % (22245)------------------------------
% 0.20/0.56  % (22245)------------------------------
% 0.20/0.56  % (22237)Refutation not found, incomplete strategy% (22237)------------------------------
% 0.20/0.56  % (22237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (22237)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (22237)Memory used [KB]: 1791
% 0.20/0.56  % (22237)Time elapsed: 0.148 s
% 0.20/0.56  % (22237)------------------------------
% 0.20/0.56  % (22237)------------------------------
% 0.20/0.56  % (22229)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (22244)Refutation not found, incomplete strategy% (22244)------------------------------
% 0.20/0.56  % (22244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (22244)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (22244)Memory used [KB]: 6396
% 0.20/0.56  % (22244)Time elapsed: 0.167 s
% 0.20/0.56  % (22244)------------------------------
% 0.20/0.56  % (22244)------------------------------
% 0.20/0.56  % (22247)Refutation not found, incomplete strategy% (22247)------------------------------
% 0.20/0.56  % (22247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (22247)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (22247)Memory used [KB]: 1663
% 0.20/0.56  % (22247)Time elapsed: 0.004 s
% 0.20/0.56  % (22247)------------------------------
% 0.20/0.56  % (22247)------------------------------
% 0.20/0.57  % (22246)Refutation not found, incomplete strategy% (22246)------------------------------
% 0.20/0.57  % (22246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (22246)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (22246)Memory used [KB]: 10874
% 0.20/0.57  % (22246)Time elapsed: 0.166 s
% 0.20/0.57  % (22246)------------------------------
% 0.20/0.57  % (22246)------------------------------
% 0.20/0.57  % (22228)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.57  % (22243)Refutation not found, incomplete strategy% (22243)------------------------------
% 0.20/0.57  % (22243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (22243)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (22243)Memory used [KB]: 6268
% 0.20/0.57  % (22243)Time elapsed: 0.149 s
% 0.20/0.57  % (22243)------------------------------
% 0.20/0.57  % (22243)------------------------------
% 0.20/0.57  % (22236)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.59  % (22228)Refutation not found, incomplete strategy% (22228)------------------------------
% 0.20/0.59  % (22228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (22228)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (22228)Memory used [KB]: 10874
% 0.20/0.59  % (22228)Time elapsed: 0.194 s
% 0.20/0.59  % (22228)------------------------------
% 0.20/0.59  % (22228)------------------------------
% 1.75/0.60  % (22225)Refutation found. Thanks to Tanya!
% 1.75/0.60  % SZS status Theorem for theBenchmark
% 1.75/0.60  % SZS output start Proof for theBenchmark
% 1.75/0.60  fof(f807,plain,(
% 1.75/0.60    $false),
% 1.75/0.60    inference(subsumption_resolution,[],[f806,f112])).
% 1.75/0.60  fof(f112,plain,(
% 1.75/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.75/0.60    inference(backward_demodulation,[],[f65,f111])).
% 1.75/0.60  fof(f111,plain,(
% 1.75/0.60    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.75/0.60    inference(resolution,[],[f73,f110])).
% 1.75/0.60  fof(f110,plain,(
% 1.75/0.60    l1_struct_0(sK0)),
% 1.75/0.60    inference(resolution,[],[f75,f64])).
% 1.75/0.60  fof(f64,plain,(
% 1.75/0.60    l1_pre_topc(sK0)),
% 1.75/0.60    inference(cnf_transformation,[],[f53])).
% 1.75/0.60  fof(f53,plain,(
% 1.75/0.60    ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.75/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).
% 1.75/0.60  fof(f51,plain,(
% 1.75/0.60    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.75/0.60    introduced(choice_axiom,[])).
% 1.75/0.60  fof(f52,plain,(
% 1.75/0.60    ? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.75/0.60    introduced(choice_axiom,[])).
% 1.75/0.60  fof(f50,plain,(
% 1.75/0.60    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.75/0.60    inference(flattening,[],[f49])).
% 1.75/0.60  fof(f49,plain,(
% 1.75/0.60    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.75/0.60    inference(nnf_transformation,[],[f29])).
% 1.75/0.60  fof(f29,plain,(
% 1.75/0.60    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.75/0.60    inference(flattening,[],[f28])).
% 1.75/0.60  fof(f28,plain,(
% 1.75/0.60    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f26])).
% 1.75/0.60  fof(f26,negated_conjecture,(
% 1.75/0.60    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.75/0.60    inference(negated_conjecture,[],[f25])).
% 1.75/0.60  fof(f25,conjecture,(
% 1.75/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).
% 1.75/0.60  fof(f75,plain,(
% 1.75/0.60    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f32])).
% 1.75/0.60  fof(f32,plain,(
% 1.75/0.60    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f17])).
% 1.75/0.60  fof(f17,axiom,(
% 1.75/0.60    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.75/0.60  fof(f73,plain,(
% 1.75/0.60    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f30])).
% 1.75/0.60  fof(f30,plain,(
% 1.75/0.60    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f15])).
% 1.75/0.60  fof(f15,axiom,(
% 1.75/0.60    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.75/0.60  fof(f65,plain,(
% 1.75/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.75/0.60    inference(cnf_transformation,[],[f53])).
% 1.75/0.60  fof(f806,plain,(
% 1.75/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.75/0.60    inference(forward_demodulation,[],[f805,f111])).
% 1.75/0.60  fof(f805,plain,(
% 1.75/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.75/0.60    inference(subsumption_resolution,[],[f804,f64])).
% 1.75/0.60  fof(f804,plain,(
% 1.75/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.75/0.60    inference(subsumption_resolution,[],[f803,f793])).
% 1.75/0.60  fof(f793,plain,(
% 1.75/0.60    ~v3_tops_1(sK1,sK0)),
% 1.75/0.60    inference(trivial_inequality_removal,[],[f791])).
% 1.75/0.60  fof(f791,plain,(
% 1.75/0.60    sK1 != sK1 | ~v3_tops_1(sK1,sK0)),
% 1.75/0.60    inference(backward_demodulation,[],[f68,f790])).
% 1.75/0.60  fof(f790,plain,(
% 1.75/0.60    sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(duplicate_literal_removal,[],[f789])).
% 1.75/0.60  fof(f789,plain,(
% 1.75/0.60    sK1 = k2_tops_1(sK0,sK1) | sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(forward_demodulation,[],[f788,f71])).
% 1.75/0.60  fof(f71,plain,(
% 1.75/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.75/0.60    inference(cnf_transformation,[],[f4])).
% 1.75/0.60  fof(f4,axiom,(
% 1.75/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.75/0.60  fof(f788,plain,(
% 1.75/0.60    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) | sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(forward_demodulation,[],[f786,f134])).
% 1.75/0.60  fof(f134,plain,(
% 1.75/0.60    ( ! [X4] : (k7_subset_1(k2_struct_0(sK0),sK1,X4) = k4_xboole_0(sK1,X4)) )),
% 1.75/0.60    inference(resolution,[],[f95,f112])).
% 1.75/0.60  fof(f95,plain,(
% 1.75/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f46])).
% 1.75/0.60  fof(f46,plain,(
% 1.75/0.60    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.75/0.60    inference(ennf_transformation,[],[f11])).
% 1.75/0.60  fof(f11,axiom,(
% 1.75/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.75/0.60  fof(f786,plain,(
% 1.75/0.60    k2_tops_1(sK0,sK1) = k7_subset_1(k2_struct_0(sK0),sK1,k1_xboole_0) | sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(backward_demodulation,[],[f741,f776])).
% 1.75/0.60  fof(f776,plain,(
% 1.75/0.60    sK1 = k2_pre_topc(sK0,sK1)),
% 1.75/0.60    inference(backward_demodulation,[],[f191,f766])).
% 1.75/0.60  fof(f766,plain,(
% 1.75/0.60    sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 1.75/0.60    inference(resolution,[],[f174,f112])).
% 1.75/0.60  fof(f174,plain,(
% 1.75/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),X0)) = X0) )),
% 1.75/0.60    inference(forward_demodulation,[],[f173,f132])).
% 1.75/0.60  fof(f132,plain,(
% 1.75/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 1.75/0.60    inference(resolution,[],[f95,f108])).
% 1.75/0.60  fof(f108,plain,(
% 1.75/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.75/0.60    inference(forward_demodulation,[],[f72,f69])).
% 1.75/0.60  fof(f69,plain,(
% 1.75/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.75/0.60    inference(cnf_transformation,[],[f6])).
% 1.75/0.60  fof(f6,axiom,(
% 1.75/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.75/0.60  fof(f72,plain,(
% 1.75/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.75/0.60    inference(cnf_transformation,[],[f8])).
% 1.75/0.60  fof(f8,axiom,(
% 1.75/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.75/0.60  fof(f173,plain,(
% 1.75/0.60    ( ! [X0] : (k4_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.75/0.60    inference(forward_demodulation,[],[f172,f132])).
% 1.75/0.60  fof(f172,plain,(
% 1.75/0.60    ( ! [X0] : (k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.75/0.60    inference(forward_demodulation,[],[f171,f111])).
% 1.75/0.60  fof(f171,plain,(
% 1.75/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0) )),
% 1.75/0.60    inference(forward_demodulation,[],[f170,f111])).
% 1.75/0.60  fof(f170,plain,(
% 1.75/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0) )),
% 1.75/0.60    inference(resolution,[],[f74,f110])).
% 1.75/0.60  fof(f74,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) )),
% 1.75/0.60    inference(cnf_transformation,[],[f31])).
% 1.75/0.60  fof(f31,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f18])).
% 1.75/0.60  fof(f18,axiom,(
% 1.75/0.60    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).
% 1.75/0.60  fof(f191,plain,(
% 1.75/0.60    k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 1.75/0.60    inference(subsumption_resolution,[],[f190,f131])).
% 1.75/0.60  fof(f131,plain,(
% 1.75/0.60    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.75/0.60    inference(backward_demodulation,[],[f118,f127])).
% 1.75/0.60  fof(f127,plain,(
% 1.75/0.60    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 1.75/0.60    inference(resolution,[],[f90,f112])).
% 1.75/0.60  fof(f90,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f44])).
% 1.75/0.60  fof(f44,plain,(
% 1.75/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.75/0.60    inference(ennf_transformation,[],[f7])).
% 1.75/0.60  fof(f7,axiom,(
% 1.75/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.75/0.60  fof(f118,plain,(
% 1.75/0.60    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.75/0.60    inference(resolution,[],[f89,f112])).
% 1.75/0.60  fof(f89,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.75/0.60    inference(cnf_transformation,[],[f43])).
% 1.75/0.60  fof(f43,plain,(
% 1.75/0.60    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.75/0.60    inference(ennf_transformation,[],[f9])).
% 1.75/0.60  fof(f9,axiom,(
% 1.75/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.75/0.60  fof(f190,plain,(
% 1.75/0.60    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 1.75/0.60    inference(forward_demodulation,[],[f189,f111])).
% 1.75/0.60  fof(f189,plain,(
% 1.75/0.60    k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.75/0.60    inference(forward_demodulation,[],[f188,f132])).
% 1.75/0.60  fof(f188,plain,(
% 1.75/0.60    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.75/0.60    inference(forward_demodulation,[],[f187,f111])).
% 1.75/0.60  fof(f187,plain,(
% 1.75/0.60    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.75/0.60    inference(subsumption_resolution,[],[f186,f64])).
% 1.75/0.60  fof(f186,plain,(
% 1.75/0.60    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.75/0.60    inference(resolution,[],[f77,f166])).
% 1.75/0.60  fof(f166,plain,(
% 1.75/0.60    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.75/0.60    inference(subsumption_resolution,[],[f165,f112])).
% 1.75/0.60  fof(f165,plain,(
% 1.75/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.75/0.60    inference(forward_demodulation,[],[f164,f111])).
% 1.75/0.60  fof(f164,plain,(
% 1.75/0.60    v3_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.75/0.60    inference(forward_demodulation,[],[f163,f132])).
% 1.75/0.60  fof(f163,plain,(
% 1.75/0.60    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.75/0.60    inference(forward_demodulation,[],[f162,f111])).
% 1.75/0.60  fof(f162,plain,(
% 1.75/0.60    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.75/0.60    inference(subsumption_resolution,[],[f161,f64])).
% 1.75/0.60  fof(f161,plain,(
% 1.75/0.60    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.75/0.60    inference(resolution,[],[f80,f66])).
% 1.75/0.60  fof(f66,plain,(
% 1.75/0.60    v4_pre_topc(sK1,sK0)),
% 1.75/0.60    inference(cnf_transformation,[],[f53])).
% 1.75/0.60  fof(f80,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f54])).
% 1.75/0.60  fof(f54,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(nnf_transformation,[],[f40])).
% 1.75/0.60  fof(f40,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f16])).
% 1.75/0.60  fof(f16,axiom,(
% 1.75/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).
% 1.75/0.60  fof(f77,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f35])).
% 1.75/0.60  fof(f35,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(flattening,[],[f34])).
% 1.75/0.60  fof(f34,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f27])).
% 1.75/0.60  fof(f27,plain,(
% 1.75/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)))))),
% 1.75/0.60    inference(pure_predicate_removal,[],[f19])).
% 1.75/0.60  fof(f19,axiom,(
% 1.75/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_pre_topc)).
% 1.75/0.60  fof(f741,plain,(
% 1.75/0.60    k2_tops_1(sK0,sK1) = k7_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) | sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(superposition,[],[f222,f210])).
% 1.75/0.60  fof(f210,plain,(
% 1.75/0.60    k1_xboole_0 = k1_tops_1(sK0,sK1) | sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(subsumption_resolution,[],[f209,f112])).
% 1.75/0.60  fof(f209,plain,(
% 1.75/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_tops_1(sK0,sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.75/0.60    inference(forward_demodulation,[],[f208,f111])).
% 1.75/0.60  fof(f208,plain,(
% 1.75/0.60    sK1 = k2_tops_1(sK0,sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.75/0.60    inference(subsumption_resolution,[],[f204,f64])).
% 1.75/0.60  fof(f204,plain,(
% 1.75/0.60    sK1 = k2_tops_1(sK0,sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.75/0.60    inference(resolution,[],[f138,f82])).
% 1.75/0.60  fof(f82,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f55])).
% 1.75/0.60  fof(f55,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(nnf_transformation,[],[f41])).
% 1.75/0.60  fof(f41,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f21])).
% 1.75/0.60  fof(f21,axiom,(
% 1.75/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.75/0.60  fof(f138,plain,(
% 1.75/0.60    v2_tops_1(sK1,sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(subsumption_resolution,[],[f137,f112])).
% 1.75/0.60  fof(f137,plain,(
% 1.75/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tops_1(sK1,sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(forward_demodulation,[],[f136,f111])).
% 1.75/0.60  fof(f136,plain,(
% 1.75/0.60    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(subsumption_resolution,[],[f135,f64])).
% 1.75/0.60  fof(f135,plain,(
% 1.75/0.60    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(resolution,[],[f78,f67])).
% 1.75/0.60  fof(f67,plain,(
% 1.75/0.60    v3_tops_1(sK1,sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(cnf_transformation,[],[f53])).
% 1.75/0.60  fof(f78,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~v3_tops_1(X1,X0) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f37])).
% 1.75/0.60  fof(f37,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(flattening,[],[f36])).
% 1.75/0.60  fof(f36,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f23])).
% 1.75/0.60  fof(f23,axiom,(
% 1.75/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).
% 1.75/0.60  fof(f222,plain,(
% 1.75/0.60    k2_tops_1(sK0,sK1) = k7_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.75/0.60    inference(resolution,[],[f177,f112])).
% 1.75/0.60  fof(f177,plain,(
% 1.75/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 1.75/0.60    inference(forward_demodulation,[],[f176,f111])).
% 1.75/0.60  fof(f176,plain,(
% 1.75/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 1.75/0.60    inference(forward_demodulation,[],[f175,f111])).
% 1.75/0.60  fof(f175,plain,(
% 1.75/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 1.75/0.60    inference(resolution,[],[f76,f64])).
% 1.75/0.60  fof(f76,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 1.75/0.60    inference(cnf_transformation,[],[f33])).
% 1.75/0.60  fof(f33,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f20])).
% 1.75/0.60  fof(f20,axiom,(
% 1.75/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.75/0.60  fof(f68,plain,(
% 1.75/0.60    ~v3_tops_1(sK1,sK0) | sK1 != k2_tops_1(sK0,sK1)),
% 1.75/0.60    inference(cnf_transformation,[],[f53])).
% 1.75/0.60  fof(f803,plain,(
% 1.75/0.60    v3_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.75/0.60    inference(subsumption_resolution,[],[f800,f66])).
% 1.75/0.60  fof(f800,plain,(
% 1.75/0.60    ~v4_pre_topc(sK1,sK0) | v3_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.75/0.60    inference(resolution,[],[f794,f79])).
% 1.75/0.60  fof(f79,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f39])).
% 1.75/0.60  fof(f39,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(flattening,[],[f38])).
% 1.75/0.60  fof(f38,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f24])).
% 1.75/0.60  fof(f24,axiom,(
% 1.75/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).
% 1.75/0.60  fof(f794,plain,(
% 1.75/0.60    v2_tops_1(sK1,sK0)),
% 1.75/0.60    inference(subsumption_resolution,[],[f792,f103])).
% 1.75/0.60  fof(f103,plain,(
% 1.75/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.75/0.60    inference(equality_resolution,[],[f93])).
% 1.75/0.60  fof(f93,plain,(
% 1.75/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.75/0.60    inference(cnf_transformation,[],[f58])).
% 1.75/0.60  fof(f58,plain,(
% 1.75/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.60    inference(flattening,[],[f57])).
% 1.75/0.60  fof(f57,plain,(
% 1.75/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.60    inference(nnf_transformation,[],[f2])).
% 1.75/0.60  fof(f2,axiom,(
% 1.75/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.75/0.60  fof(f792,plain,(
% 1.75/0.60    ~r1_tarski(sK1,sK1) | v2_tops_1(sK1,sK0)),
% 1.75/0.60    inference(backward_demodulation,[],[f218,f790])).
% 1.75/0.60  fof(f218,plain,(
% 1.75/0.60    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 1.75/0.60    inference(resolution,[],[f142,f112])).
% 1.75/0.60  fof(f142,plain,(
% 1.75/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k2_tops_1(sK0,X0)) | v2_tops_1(X0,sK0)) )),
% 1.75/0.60    inference(forward_demodulation,[],[f141,f111])).
% 1.75/0.60  fof(f141,plain,(
% 1.75/0.60    ( ! [X0] : (~r1_tarski(X0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) )),
% 1.75/0.60    inference(resolution,[],[f85,f64])).
% 1.75/0.60  fof(f85,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f56])).
% 1.75/0.60  fof(f56,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(nnf_transformation,[],[f42])).
% 1.75/0.60  fof(f42,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f22])).
% 1.75/0.60  fof(f22,axiom,(
% 1.75/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.75/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 1.75/0.60  % SZS output end Proof for theBenchmark
% 1.75/0.60  % (22225)------------------------------
% 1.75/0.60  % (22225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (22225)Termination reason: Refutation
% 1.75/0.60  
% 1.75/0.60  % (22225)Memory used [KB]: 2302
% 1.75/0.60  % (22225)Time elapsed: 0.159 s
% 1.75/0.60  % (22225)------------------------------
% 1.75/0.60  % (22225)------------------------------
% 1.75/0.60  % (22217)Success in time 0.255 s
%------------------------------------------------------------------------------
