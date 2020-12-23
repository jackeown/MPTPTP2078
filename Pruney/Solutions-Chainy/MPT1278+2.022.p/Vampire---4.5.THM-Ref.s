%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:52 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 188 expanded)
%              Number of leaves         :   17 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  247 ( 920 expanded)
%              Number of equality atoms :   37 ( 155 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f113,f118,f128,f149,f201,f213])).

fof(f213,plain,
    ( ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f211,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != sK1
    & v3_tops_1(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & v3_tops_1(X1,sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK1
      & v3_tops_1(sK1,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f211,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f210,f126])).

fof(f126,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_8 ),
    inference(resolution,[],[f112,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f112,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl2_8
  <=> v1_xboole_0(k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f210,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f209,f89])).

fof(f89,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f209,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f208,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f208,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f205,f30])).

fof(f205,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10 ),
    inference(superposition,[],[f37,f148])).

fof(f148,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl2_10
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f201,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl2_9 ),
    inference(subsumption_resolution,[],[f144,f88])).

fof(f88,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f30,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f144,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_9
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f149,plain,
    ( ~ spl2_9
    | spl2_10
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f140,f70,f146,f142])).

fof(f70,plain,
    ( spl2_4
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f140,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f139,f29])).

fof(f139,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f72,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f72,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f128,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f68,f30])).

fof(f68,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f118,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f116,f29])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(subsumption_resolution,[],[f115,f30])).

fof(f115,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(subsumption_resolution,[],[f114,f32])).

fof(f32,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(resolution,[],[f78,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

fof(f78,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_5
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f113,plain,
    ( ~ spl2_5
    | spl2_8 ),
    inference(avatar_split_clause,[],[f108,f110,f77])).

fof(f108,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f87,f29])).

fof(f87,plain,
    ( v1_xboole_0(k1_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_tops_1(X1,X0)
        & l1_pre_topc(X0) )
     => v1_xboole_0(k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_tops_1)).

fof(f73,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f64,f70,f66])).

fof(f64,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f63,f29])).

fof(f63,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f31,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:38:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.42  % (18180)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.42  % (18180)Refutation found. Thanks to Tanya!
% 0.18/0.42  % SZS status Theorem for theBenchmark
% 0.18/0.42  % SZS output start Proof for theBenchmark
% 0.18/0.42  fof(f214,plain,(
% 0.18/0.42    $false),
% 0.18/0.42    inference(avatar_sat_refutation,[],[f73,f113,f118,f128,f149,f201,f213])).
% 0.18/0.42  fof(f213,plain,(
% 0.18/0.42    ~spl2_8 | ~spl2_10),
% 0.18/0.42    inference(avatar_contradiction_clause,[],[f212])).
% 0.18/0.42  fof(f212,plain,(
% 0.18/0.42    $false | (~spl2_8 | ~spl2_10)),
% 0.18/0.42    inference(subsumption_resolution,[],[f211,f33])).
% 0.18/0.42  fof(f33,plain,(
% 0.18/0.42    k1_xboole_0 != sK1),
% 0.18/0.42    inference(cnf_transformation,[],[f26])).
% 0.18/0.42  fof(f26,plain,(
% 0.18/0.42    (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.18/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f25,f24])).
% 0.18/0.42  fof(f24,plain,(
% 0.18/0.42    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f25,plain,(
% 0.18/0.42    ? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f12,plain,(
% 0.18/0.42    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.18/0.42    inference(flattening,[],[f11])).
% 0.18/0.42  fof(f11,plain,(
% 0.18/0.42    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f10])).
% 0.18/0.42  fof(f10,negated_conjecture,(
% 0.18/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.18/0.42    inference(negated_conjecture,[],[f9])).
% 0.18/0.42  fof(f9,conjecture,(
% 0.18/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 0.18/0.42  fof(f211,plain,(
% 0.18/0.42    k1_xboole_0 = sK1 | (~spl2_8 | ~spl2_10)),
% 0.18/0.42    inference(forward_demodulation,[],[f210,f126])).
% 0.18/0.42  fof(f126,plain,(
% 0.18/0.42    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_8),
% 0.18/0.42    inference(resolution,[],[f112,f38])).
% 0.18/0.42  fof(f38,plain,(
% 0.18/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f17])).
% 0.18/0.42  fof(f17,plain,(
% 0.18/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f1])).
% 0.18/0.42  fof(f1,axiom,(
% 0.18/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.18/0.42  fof(f112,plain,(
% 0.18/0.42    v1_xboole_0(k1_tops_1(sK0,sK1)) | ~spl2_8),
% 0.18/0.42    inference(avatar_component_clause,[],[f110])).
% 0.18/0.42  fof(f110,plain,(
% 0.18/0.42    spl2_8 <=> v1_xboole_0(k1_tops_1(sK0,sK1))),
% 0.18/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.18/0.42  fof(f210,plain,(
% 0.18/0.42    sK1 = k1_tops_1(sK0,sK1) | ~spl2_10),
% 0.18/0.42    inference(forward_demodulation,[],[f209,f89])).
% 0.18/0.42  fof(f89,plain,(
% 0.18/0.42    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.18/0.42    inference(resolution,[],[f30,f34])).
% 0.18/0.42  fof(f34,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.42    inference(cnf_transformation,[],[f13])).
% 0.18/0.42  fof(f13,plain,(
% 0.18/0.42    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f3])).
% 0.18/0.42  fof(f3,axiom,(
% 0.18/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.18/0.42  fof(f30,plain,(
% 0.18/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.42    inference(cnf_transformation,[],[f26])).
% 0.18/0.42  fof(f209,plain,(
% 0.18/0.42    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_10),
% 0.18/0.42    inference(subsumption_resolution,[],[f208,f29])).
% 0.18/0.42  fof(f29,plain,(
% 0.18/0.42    l1_pre_topc(sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f26])).
% 0.18/0.42  fof(f208,plain,(
% 0.18/0.42    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~spl2_10),
% 0.18/0.42    inference(subsumption_resolution,[],[f205,f30])).
% 0.18/0.42  fof(f205,plain,(
% 0.18/0.42    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_10),
% 0.18/0.42    inference(superposition,[],[f37,f148])).
% 0.18/0.42  fof(f148,plain,(
% 0.18/0.42    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_10),
% 0.18/0.42    inference(avatar_component_clause,[],[f146])).
% 0.18/0.42  fof(f146,plain,(
% 0.18/0.42    spl2_10 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.18/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.18/0.42  fof(f37,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f16])).
% 0.18/0.42  fof(f16,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f5])).
% 0.18/0.42  fof(f5,axiom,(
% 0.18/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.18/0.42  fof(f201,plain,(
% 0.18/0.42    spl2_9),
% 0.18/0.42    inference(avatar_contradiction_clause,[],[f200])).
% 0.18/0.42  fof(f200,plain,(
% 0.18/0.42    $false | spl2_9),
% 0.18/0.42    inference(subsumption_resolution,[],[f144,f88])).
% 0.18/0.42  fof(f88,plain,(
% 0.18/0.42    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.42    inference(resolution,[],[f30,f43])).
% 0.18/0.42  fof(f43,plain,(
% 0.18/0.42    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.42    inference(cnf_transformation,[],[f23])).
% 0.18/0.42  fof(f23,plain,(
% 0.18/0.42    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f2])).
% 0.18/0.42  fof(f2,axiom,(
% 0.18/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.18/0.42  fof(f144,plain,(
% 0.18/0.42    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_9),
% 0.18/0.42    inference(avatar_component_clause,[],[f142])).
% 0.18/0.42  fof(f142,plain,(
% 0.18/0.42    spl2_9 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.18/0.42  fof(f149,plain,(
% 0.18/0.42    ~spl2_9 | spl2_10 | ~spl2_4),
% 0.18/0.42    inference(avatar_split_clause,[],[f140,f70,f146,f142])).
% 0.18/0.42  fof(f70,plain,(
% 0.18/0.42    spl2_4 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.18/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.18/0.42  fof(f140,plain,(
% 0.18/0.42    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.18/0.42    inference(subsumption_resolution,[],[f139,f29])).
% 0.18/0.42  fof(f139,plain,(
% 0.18/0.42    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.18/0.42    inference(resolution,[],[f72,f35])).
% 0.18/0.42  fof(f35,plain,(
% 0.18/0.42    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f15])).
% 0.18/0.42  fof(f15,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.42    inference(flattening,[],[f14])).
% 0.18/0.42  fof(f14,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f4])).
% 0.18/0.42  fof(f4,axiom,(
% 0.18/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.18/0.42  fof(f72,plain,(
% 0.18/0.42    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_4),
% 0.18/0.42    inference(avatar_component_clause,[],[f70])).
% 0.18/0.42  fof(f128,plain,(
% 0.18/0.42    spl2_3),
% 0.18/0.42    inference(avatar_contradiction_clause,[],[f127])).
% 0.18/0.42  fof(f127,plain,(
% 0.18/0.42    $false | spl2_3),
% 0.18/0.42    inference(subsumption_resolution,[],[f68,f30])).
% 0.18/0.42  fof(f68,plain,(
% 0.18/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_3),
% 0.18/0.42    inference(avatar_component_clause,[],[f66])).
% 0.18/0.42  fof(f66,plain,(
% 0.18/0.42    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.18/0.42  fof(f118,plain,(
% 0.18/0.42    spl2_5),
% 0.18/0.42    inference(avatar_contradiction_clause,[],[f117])).
% 0.18/0.42  fof(f117,plain,(
% 0.18/0.42    $false | spl2_5),
% 0.18/0.42    inference(subsumption_resolution,[],[f116,f29])).
% 0.18/0.42  fof(f116,plain,(
% 0.18/0.42    ~l1_pre_topc(sK0) | spl2_5),
% 0.18/0.42    inference(subsumption_resolution,[],[f115,f30])).
% 0.18/0.42  fof(f115,plain,(
% 0.18/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_5),
% 0.18/0.42    inference(subsumption_resolution,[],[f114,f32])).
% 0.18/0.42  fof(f32,plain,(
% 0.18/0.42    v3_tops_1(sK1,sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f26])).
% 0.18/0.42  fof(f114,plain,(
% 0.18/0.42    ~v3_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_5),
% 0.18/0.42    inference(resolution,[],[f78,f39])).
% 0.18/0.42  fof(f39,plain,(
% 0.18/0.42    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f19])).
% 0.18/0.42  fof(f19,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.42    inference(flattening,[],[f18])).
% 0.18/0.42  fof(f18,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f8])).
% 0.18/0.42  fof(f8,axiom,(
% 0.18/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).
% 0.18/0.42  fof(f78,plain,(
% 0.18/0.42    ~v2_tops_1(sK1,sK0) | spl2_5),
% 0.18/0.42    inference(avatar_component_clause,[],[f77])).
% 0.18/0.42  fof(f77,plain,(
% 0.18/0.42    spl2_5 <=> v2_tops_1(sK1,sK0)),
% 0.18/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.18/0.42  fof(f113,plain,(
% 0.18/0.42    ~spl2_5 | spl2_8),
% 0.18/0.42    inference(avatar_split_clause,[],[f108,f110,f77])).
% 0.18/0.42  fof(f108,plain,(
% 0.18/0.42    v1_xboole_0(k1_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f87,f29])).
% 0.18/0.42  fof(f87,plain,(
% 0.18/0.42    v1_xboole_0(k1_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.18/0.42    inference(resolution,[],[f30,f42])).
% 0.18/0.42  fof(f42,plain,(
% 0.18/0.42    ( ! [X0,X1] : (v1_xboole_0(k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f22])).
% 0.18/0.42  fof(f22,plain,(
% 0.18/0.42    ! [X0,X1] : (v1_xboole_0(k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | ~l1_pre_topc(X0))),
% 0.18/0.42    inference(flattening,[],[f21])).
% 0.18/0.42  fof(f21,plain,(
% 0.18/0.42    ! [X0,X1] : (v1_xboole_0(k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | ~l1_pre_topc(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f6])).
% 0.18/0.42  fof(f6,axiom,(
% 0.18/0.42    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_tops_1(X1,X0) & l1_pre_topc(X0)) => v1_xboole_0(k1_tops_1(X0,X1)))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_tops_1)).
% 0.18/0.42  fof(f73,plain,(
% 0.18/0.42    ~spl2_3 | spl2_4),
% 0.18/0.42    inference(avatar_split_clause,[],[f64,f70,f66])).
% 0.18/0.42  fof(f64,plain,(
% 0.18/0.42    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.42    inference(subsumption_resolution,[],[f63,f29])).
% 0.18/0.42  fof(f63,plain,(
% 0.18/0.42    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.18/0.42    inference(resolution,[],[f31,f40])).
% 0.18/0.42  fof(f40,plain,(
% 0.18/0.42    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f27])).
% 0.18/0.42  fof(f27,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.42    inference(nnf_transformation,[],[f20])).
% 0.18/0.42  fof(f20,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.42    inference(ennf_transformation,[],[f7])).
% 0.18/0.42  fof(f7,axiom,(
% 0.18/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 0.18/0.42  fof(f31,plain,(
% 0.18/0.42    v3_pre_topc(sK1,sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f26])).
% 0.18/0.42  % SZS output end Proof for theBenchmark
% 0.18/0.42  % (18180)------------------------------
% 0.18/0.42  % (18180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.42  % (18180)Termination reason: Refutation
% 0.18/0.42  
% 0.18/0.42  % (18180)Memory used [KB]: 6140
% 0.18/0.42  % (18180)Time elapsed: 0.008 s
% 0.18/0.42  % (18180)------------------------------
% 0.18/0.42  % (18180)------------------------------
% 0.18/0.43  % (18160)Success in time 0.084 s
%------------------------------------------------------------------------------
