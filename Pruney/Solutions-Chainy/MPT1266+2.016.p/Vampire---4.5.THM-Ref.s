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
% DateTime   : Thu Dec  3 13:12:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 433 expanded)
%              Number of leaves         :   26 ( 140 expanded)
%              Depth                    :   15
%              Number of atoms          :  359 (1652 expanded)
%              Number of equality atoms :   72 ( 477 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2073,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f63,f88,f90,f225,f622,f864,f1033,f1057,f1728,f1997,f2016,f2018,f2072])).

fof(f2072,plain,
    ( spl2_2
    | ~ spl2_115
    | ~ spl2_164 ),
    inference(avatar_contradiction_clause,[],[f2071])).

fof(f2071,plain,
    ( $false
    | spl2_2
    | ~ spl2_115
    | ~ spl2_164 ),
    inference(subsumption_resolution,[],[f2070,f61])).

fof(f61,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f2070,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_115
    | ~ spl2_164 ),
    inference(forward_demodulation,[],[f2069,f75])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) ),
    inference(forward_demodulation,[],[f71,f65])).

fof(f65,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f64,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f42,f40])).

fof(f40,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f51,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2069,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_115
    | ~ spl2_164 ),
    inference(forward_demodulation,[],[f1791,f1051])).

fof(f1051,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_115 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1049,plain,
    ( spl2_115
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).

fof(f1791,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_164 ),
    inference(resolution,[],[f1727,f68])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f36,f67])).

fof(f67,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f66,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
          | ~ v2_tops_1(X1,sK0) )
        & ( k1_xboole_0 = k1_tops_1(sK0,X1)
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
        | ~ v2_tops_1(sK1,sK0) )
      & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (21347)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f1727,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) )
    | ~ spl2_164 ),
    inference(avatar_component_clause,[],[f1726])).

fof(f1726,plain,
    ( spl2_164
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_164])])).

fof(f2018,plain,
    ( spl2_115
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_89 ),
    inference(avatar_split_clause,[],[f1084,f862,f223,f55,f1049])).

fof(f55,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f223,plain,
    ( spl2_17
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ v1_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f862,plain,
    ( spl2_89
  <=> ! [X0] :
        ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).

fof(f1084,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_17
    | ~ spl2_89 ),
    inference(resolution,[],[f897,f68])).

fof(f897,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tops_1(X0,sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) )
    | ~ spl2_17
    | ~ spl2_89 ),
    inference(duplicate_literal_removal,[],[f878])).

fof(f878,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tops_1(X0,sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_17
    | ~ spl2_89 ),
    inference(resolution,[],[f863,f239])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_17 ),
    inference(resolution,[],[f224,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ v1_tops_1(X0,sK0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f223])).

fof(f863,plain,
    ( ! [X0] :
        ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tops_1(X0,sK0) )
    | ~ spl2_89 ),
    inference(avatar_component_clause,[],[f862])).

fof(f2016,plain,
    ( ~ spl2_3
    | ~ spl2_114
    | ~ spl2_66
    | spl2_1 ),
    inference(avatar_split_clause,[],[f2015,f55,f617,f1045,f82])).

fof(f82,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1045,plain,
    ( spl2_114
  <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_114])])).

fof(f617,plain,
    ( spl2_66
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f2015,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(forward_demodulation,[],[f1244,f67])).

fof(f1244,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(forward_demodulation,[],[f1200,f67])).

fof(f1200,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(resolution,[],[f49,f57])).

fof(f57,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f1997,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | ~ spl2_101
    | spl2_115
    | ~ spl2_164 ),
    inference(avatar_contradiction_clause,[],[f1974])).

fof(f1974,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_101
    | spl2_115
    | ~ spl2_164 ),
    inference(subsumption_resolution,[],[f1050,f1973])).

fof(f1973,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_101
    | ~ spl2_164 ),
    inference(forward_demodulation,[],[f1966,f65])).

fof(f1966,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_101
    | ~ spl2_164 ),
    inference(backward_demodulation,[],[f1041,f1965])).

fof(f1965,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_164 ),
    inference(forward_demodulation,[],[f1791,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f1041,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))
    | ~ spl2_4
    | ~ spl2_101 ),
    inference(resolution,[],[f954,f92])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f87,f51])).

fof(f87,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_4
  <=> ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f954,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_101 ),
    inference(avatar_component_clause,[],[f953])).

fof(f953,plain,
    ( spl2_101
  <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).

fof(f1050,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | spl2_115 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1728,plain,
    ( ~ spl2_3
    | spl2_164 ),
    inference(avatar_split_clause,[],[f1721,f1726,f82])).

fof(f1721,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f45,f67])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f1057,plain,
    ( ~ spl2_3
    | ~ spl2_115
    | ~ spl2_101
    | spl2_114 ),
    inference(avatar_split_clause,[],[f1056,f1045,f953,f1049,f82])).

fof(f1056,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | spl2_114 ),
    inference(forward_demodulation,[],[f1055,f67])).

fof(f1055,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_114 ),
    inference(resolution,[],[f1047,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f1047,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl2_114 ),
    inference(avatar_component_clause,[],[f1045])).

fof(f1033,plain,(
    spl2_101 ),
    inference(avatar_contradiction_clause,[],[f1032])).

fof(f1032,plain,
    ( $false
    | spl2_101 ),
    inference(subsumption_resolution,[],[f68,f1030])).

fof(f1030,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_101 ),
    inference(resolution,[],[f955,f50])).

fof(f955,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_101 ),
    inference(avatar_component_clause,[],[f953])).

fof(f864,plain,
    ( ~ spl2_3
    | spl2_89 ),
    inference(avatar_split_clause,[],[f823,f862,f82])).

fof(f823,plain,(
    ! [X0] :
      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f48,f67])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f622,plain,(
    spl2_66 ),
    inference(avatar_contradiction_clause,[],[f621])).

fof(f621,plain,
    ( $false
    | spl2_66 ),
    inference(subsumption_resolution,[],[f68,f619])).

fof(f619,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_66 ),
    inference(avatar_component_clause,[],[f617])).

fof(f225,plain,
    ( ~ spl2_3
    | spl2_17 ),
    inference(avatar_split_clause,[],[f220,f223,f82])).

fof(f220,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f46,f67])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f35,f84])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f88,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f80,f86,f82])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f52,f67])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f63,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f37,f59,f55])).

fof(f37,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f38,f59,f55])).

fof(f38,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.43  % (21362)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.46  % (21350)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (21361)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (21353)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.46  % (21348)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (21356)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (21346)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (21349)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (21362)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f2073,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f62,f63,f88,f90,f225,f622,f864,f1033,f1057,f1728,f1997,f2016,f2018,f2072])).
% 0.22/0.48  fof(f2072,plain,(
% 0.22/0.48    spl2_2 | ~spl2_115 | ~spl2_164),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f2071])).
% 0.22/0.48  fof(f2071,plain,(
% 0.22/0.48    $false | (spl2_2 | ~spl2_115 | ~spl2_164)),
% 0.22/0.48    inference(subsumption_resolution,[],[f2070,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f2070,plain,(
% 0.22/0.48    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_115 | ~spl2_164)),
% 0.22/0.48    inference(forward_demodulation,[],[f2069,f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f71,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(forward_demodulation,[],[f64,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f42,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))) )),
% 0.22/0.48    inference(resolution,[],[f51,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.48  fof(f2069,plain,(
% 0.22/0.48    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_115 | ~spl2_164)),
% 0.22/0.48    inference(forward_demodulation,[],[f1791,f1051])).
% 0.22/0.48  fof(f1051,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl2_115),
% 0.22/0.48    inference(avatar_component_clause,[],[f1049])).
% 0.22/0.48  fof(f1049,plain,(
% 0.22/0.48    spl2_115 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).
% 0.22/0.48  fof(f1791,plain,(
% 0.22/0.48    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~spl2_164),
% 0.22/0.48    inference(resolution,[],[f1727,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.48    inference(backward_demodulation,[],[f36,f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.48    inference(resolution,[],[f66,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.22/0.48    inference(negated_conjecture,[],[f14])).
% 0.22/0.48  fof(f14,conjecture,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.48    inference(resolution,[],[f43,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  % (21347)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f1727,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)) ) | ~spl2_164),
% 0.22/0.48    inference(avatar_component_clause,[],[f1726])).
% 0.22/0.48  fof(f1726,plain,(
% 0.22/0.48    spl2_164 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_164])])).
% 0.22/0.48  fof(f2018,plain,(
% 0.22/0.48    spl2_115 | ~spl2_1 | ~spl2_17 | ~spl2_89),
% 0.22/0.48    inference(avatar_split_clause,[],[f1084,f862,f223,f55,f1049])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f223,plain,(
% 0.22/0.48    spl2_17 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.48  fof(f862,plain,(
% 0.22/0.48    spl2_89 <=> ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(X0,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).
% 0.22/0.48  fof(f1084,plain,(
% 0.22/0.48    ~v2_tops_1(sK1,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | (~spl2_17 | ~spl2_89)),
% 0.22/0.48    inference(resolution,[],[f897,f68])).
% 0.22/0.48  fof(f897,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) | (~spl2_17 | ~spl2_89)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f878])).
% 0.22/0.48  fof(f878,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_17 | ~spl2_89)),
% 0.22/0.48    inference(resolution,[],[f863,f239])).
% 0.22/0.48  fof(f239,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl2_17),
% 0.22/0.48    inference(resolution,[],[f224,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.48  fof(f224,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) ) | ~spl2_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f223])).
% 0.22/0.48  fof(f863,plain,(
% 0.22/0.48    ( ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(X0,sK0)) ) | ~spl2_89),
% 0.22/0.48    inference(avatar_component_clause,[],[f862])).
% 0.22/0.48  fof(f2016,plain,(
% 0.22/0.48    ~spl2_3 | ~spl2_114 | ~spl2_66 | spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f2015,f55,f617,f1045,f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl2_3 <=> l1_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f1045,plain,(
% 0.22/0.48    spl2_114 <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_114])])).
% 0.22/0.48  fof(f617,plain,(
% 0.22/0.48    spl2_66 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).
% 0.22/0.48  fof(f2015,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | spl2_1),
% 0.22/0.48    inference(forward_demodulation,[],[f1244,f67])).
% 0.22/0.48  fof(f1244,plain,(
% 0.22/0.48    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_1),
% 0.22/0.48    inference(forward_demodulation,[],[f1200,f67])).
% 0.22/0.48  fof(f1200,plain,(
% 0.22/0.48    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_1),
% 0.22/0.48    inference(resolution,[],[f49,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ~v2_tops_1(sK1,sK0) | spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f55])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 0.22/0.48  fof(f1997,plain,(
% 0.22/0.48    ~spl2_2 | ~spl2_4 | ~spl2_101 | spl2_115 | ~spl2_164),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f1974])).
% 0.22/0.48  fof(f1974,plain,(
% 0.22/0.48    $false | (~spl2_2 | ~spl2_4 | ~spl2_101 | spl2_115 | ~spl2_164)),
% 0.22/0.48    inference(subsumption_resolution,[],[f1050,f1973])).
% 0.22/0.48  fof(f1973,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_4 | ~spl2_101 | ~spl2_164)),
% 0.22/0.48    inference(forward_demodulation,[],[f1966,f65])).
% 0.22/0.48  fof(f1966,plain,(
% 0.22/0.48    k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_4 | ~spl2_101 | ~spl2_164)),
% 0.22/0.48    inference(backward_demodulation,[],[f1041,f1965])).
% 0.22/0.48  fof(f1965,plain,(
% 0.22/0.48    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_164)),
% 0.22/0.48    inference(forward_demodulation,[],[f1791,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f59])).
% 0.22/0.48  fof(f1041,plain,(
% 0.22/0.48    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) | (~spl2_4 | ~spl2_101)),
% 0.22/0.48    inference(resolution,[],[f954,f92])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)))) ) | ~spl2_4),
% 0.22/0.48    inference(resolution,[],[f87,f51])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl2_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl2_4 <=> ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.48  fof(f954,plain,(
% 0.22/0.48    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_101),
% 0.22/0.48    inference(avatar_component_clause,[],[f953])).
% 0.22/0.48  fof(f953,plain,(
% 0.22/0.48    spl2_101 <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).
% 0.22/0.48  fof(f1050,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | spl2_115),
% 0.22/0.48    inference(avatar_component_clause,[],[f1049])).
% 0.22/0.48  fof(f1728,plain,(
% 0.22/0.48    ~spl2_3 | spl2_164),
% 0.22/0.48    inference(avatar_split_clause,[],[f1721,f1726,f82])).
% 0.22/0.48  fof(f1721,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) | ~l1_pre_topc(sK0)) )),
% 0.22/0.48    inference(superposition,[],[f45,f67])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.22/0.48  fof(f1057,plain,(
% 0.22/0.48    ~spl2_3 | ~spl2_115 | ~spl2_101 | spl2_114),
% 0.22/0.48    inference(avatar_split_clause,[],[f1056,f1045,f953,f1049,f82])).
% 0.22/0.48  fof(f1056,plain,(
% 0.22/0.48    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | spl2_114),
% 0.22/0.48    inference(forward_demodulation,[],[f1055,f67])).
% 0.22/0.48  fof(f1055,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_114),
% 0.22/0.48    inference(resolution,[],[f1047,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.22/0.48  fof(f1047,plain,(
% 0.22/0.48    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | spl2_114),
% 0.22/0.48    inference(avatar_component_clause,[],[f1045])).
% 0.22/0.48  fof(f1033,plain,(
% 0.22/0.48    spl2_101),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f1032])).
% 0.22/0.48  fof(f1032,plain,(
% 0.22/0.48    $false | spl2_101),
% 0.22/0.48    inference(subsumption_resolution,[],[f68,f1030])).
% 0.22/0.48  fof(f1030,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_101),
% 0.22/0.48    inference(resolution,[],[f955,f50])).
% 0.22/0.48  fof(f955,plain,(
% 0.22/0.48    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_101),
% 0.22/0.48    inference(avatar_component_clause,[],[f953])).
% 0.22/0.48  fof(f864,plain,(
% 0.22/0.48    ~spl2_3 | spl2_89),
% 0.22/0.48    inference(avatar_split_clause,[],[f823,f862,f82])).
% 0.22/0.48  fof(f823,plain,(
% 0.22/0.48    ( ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.22/0.48    inference(superposition,[],[f48,f67])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f622,plain,(
% 0.22/0.48    spl2_66),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f621])).
% 0.22/0.48  fof(f621,plain,(
% 0.22/0.48    $false | spl2_66),
% 0.22/0.48    inference(subsumption_resolution,[],[f68,f619])).
% 0.22/0.48  fof(f619,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_66),
% 0.22/0.48    inference(avatar_component_clause,[],[f617])).
% 0.22/0.48  fof(f225,plain,(
% 0.22/0.48    ~spl2_3 | spl2_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f220,f223,f82])).
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~l1_pre_topc(sK0)) )),
% 0.22/0.48    inference(superposition,[],[f46,f67])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl2_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    $false | spl2_3),
% 0.22/0.48    inference(subsumption_resolution,[],[f35,f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f82])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ~spl2_3 | spl2_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f80,f86,f82])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.22/0.48    inference(superposition,[],[f52,f67])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl2_1 | spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f37,f59,f55])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ~spl2_1 | ~spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f59,f55])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (21362)------------------------------
% 0.22/0.48  % (21362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (21362)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (21352)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (21362)Memory used [KB]: 7291
% 0.22/0.48  % (21362)Time elapsed: 0.069 s
% 0.22/0.48  % (21362)------------------------------
% 0.22/0.48  % (21362)------------------------------
% 0.22/0.48  % (21345)Success in time 0.124 s
%------------------------------------------------------------------------------
