%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 175 expanded)
%              Number of leaves         :   24 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  295 ( 459 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f56,f64,f68,f72,f81,f85,f95,f102,f106,f116,f126,f135,f142])).

fof(f142,plain,
    ( ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f140,f115])).

fof(f115,plain,
    ( sK0 = k4_tarski(sK4(sK0),sK5(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_11
  <=> sK0 = k4_tarski(sK4(sK0),sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f140,plain,
    ( sK0 != k4_tarski(sK4(sK0),sK5(sK0))
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(resolution,[],[f127,f134])).

fof(f134,plain,
    ( r2_hidden(sK5(sK0),sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_13
  <=> r2_hidden(sK5(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 != k4_tarski(sK4(sK0),X0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f125,f27])).

fof(f27,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK1)
      | k4_tarski(X4,X5) != sK0
      | ~ r2_hidden(X5,sK2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1)
          | k4_tarski(X4,X5) != X0 )
      & r2_hidden(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ~ ( ! [X4,X5] :
                ~ ( r2_hidden(X5,X2)
                  & r2_hidden(X4,X1)
                  & k4_tarski(X4,X5) = X0 )
            & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f125,plain,
    ( r2_hidden(sK4(sK0),sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_12
  <=> r2_hidden(sK4(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f135,plain,
    ( spl6_13
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f131,f114,f104,f62,f48,f133])).

fof(f48,plain,
    ( spl6_1
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f62,plain,
    ( spl6_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f104,plain,
    ( spl6_10
  <=> sK3 = k5_relat_1(sK3,k6_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f131,plain,
    ( r2_hidden(sK5(sK0),sK2)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f130,f49])).

fof(f49,plain,
    ( r2_hidden(sK0,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f130,plain,
    ( ~ r2_hidden(sK0,sK3)
    | r2_hidden(sK5(sK0),sK2)
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(superposition,[],[f112,f115])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | r2_hidden(X1,sK2) )
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f110,f63])).

fof(f63,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | r2_hidden(X1,sK2)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_10 ),
    inference(superposition,[],[f36,f105])).

fof(f105,plain,
    ( sK3 = k5_relat_1(sK3,k6_relat_1(sK2))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).

fof(f126,plain,
    ( spl6_12
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f122,f114,f100,f62,f48,f124])).

fof(f100,plain,
    ( spl6_9
  <=> sK3 = k5_relat_1(k6_relat_1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f122,plain,
    ( r2_hidden(sK4(sK0),sK1)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f121,f49])).

fof(f121,plain,
    ( ~ r2_hidden(sK0,sK3)
    | r2_hidden(sK4(sK0),sK1)
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(superposition,[],[f109,f115])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | r2_hidden(X0,sK1) )
    | ~ spl6_3
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f107,f63])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_9 ),
    inference(superposition,[],[f33,f101])).

fof(f101,plain,
    ( sK3 = k5_relat_1(k6_relat_1(sK1),sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

fof(f116,plain,
    ( spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f96,f93,f114])).

fof(f93,plain,
    ( spl6_8
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f96,plain,
    ( sK0 = k4_tarski(sK4(sK0),sK5(sK0))
    | ~ spl6_8 ),
    inference(resolution,[],[f94,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f94,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f106,plain,
    ( spl6_10
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f91,f83,f62,f104])).

fof(f83,plain,
    ( spl6_7
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f91,plain,
    ( sK3 = k5_relat_1(sK3,k6_relat_1(sK2))
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f90,f63])).

fof(f90,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k5_relat_1(sK3,k6_relat_1(sK2))
    | ~ spl6_7 ),
    inference(resolution,[],[f84,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f84,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f102,plain,
    ( spl6_9
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f88,f79,f62,f100])).

fof(f79,plain,
    ( spl6_6
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f88,plain,
    ( sK3 = k5_relat_1(k6_relat_1(sK1),sK3)
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f87,f63])).

fof(f87,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k5_relat_1(k6_relat_1(sK1),sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f80,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f80,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f95,plain,
    ( spl6_8
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f77,f54,f48,f93])).

fof(f54,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f77,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f60,f49])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k2_zfmisc_1(sK1,sK2)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f55,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f85,plain,
    ( spl6_7
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f76,f70,f62,f83])).

fof(f70,plain,
    ( spl6_5
  <=> v5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f76,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f75,f63])).

fof(f75,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f71,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f71,plain,
    ( v5_relat_1(sK3,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f81,plain,
    ( spl6_6
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f74,f66,f62,f79])).

fof(f66,plain,
    ( spl6_4
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f74,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f73,f63])).

fof(f73,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl6_4 ),
    inference(resolution,[],[f67,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

% (8355)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f67,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f72,plain,
    ( spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f59,f54,f70])).

fof(f59,plain,
    ( v5_relat_1(sK3,sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f68,plain,
    ( spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f58,f54,f66])).

fof(f58,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f55,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,
    ( spl6_3
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f57,f54,f62])).

fof(f57,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f56,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f29,f48])).

fof(f29,plain,(
    r2_hidden(sK0,sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:42:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (8349)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (8363)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (8349)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (8357)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f50,f56,f64,f68,f72,f81,f85,f95,f102,f106,f116,f126,f135,f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ~spl6_11 | ~spl6_12 | ~spl6_13),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    $false | (~spl6_11 | ~spl6_12 | ~spl6_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f140,f115])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    sK0 = k4_tarski(sK4(sK0),sK5(sK0)) | ~spl6_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl6_11 <=> sK0 = k4_tarski(sK4(sK0),sK5(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    sK0 != k4_tarski(sK4(sK0),sK5(sK0)) | (~spl6_12 | ~spl6_13)),
% 0.21/0.49    inference(resolution,[],[f127,f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    r2_hidden(sK5(sK0),sK2) | ~spl6_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl6_13 <=> r2_hidden(sK5(sK0),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK2) | sK0 != k4_tarski(sK4(sK0),X0)) ) | ~spl6_12),
% 0.21/0.49    inference(resolution,[],[f125,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r2_hidden(X4,sK1) | k4_tarski(X4,X5) != sK0 | ~r2_hidden(X5,sK2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((! [X4,X5] : (~r2_hidden(X5,X2) | ~r2_hidden(X4,X1) | k4_tarski(X4,X5) != X0) & r2_hidden(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    r2_hidden(sK4(sK0),sK1) | ~spl6_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl6_12 <=> r2_hidden(sK4(sK0),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl6_13 | ~spl6_1 | ~spl6_3 | ~spl6_10 | ~spl6_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f131,f114,f104,f62,f48,f133])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl6_1 <=> r2_hidden(sK0,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl6_3 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl6_10 <=> sK3 = k5_relat_1(sK3,k6_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    r2_hidden(sK5(sK0),sK2) | (~spl6_1 | ~spl6_3 | ~spl6_10 | ~spl6_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    r2_hidden(sK0,sK3) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f48])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK3) | r2_hidden(sK5(sK0),sK2) | (~spl6_3 | ~spl6_10 | ~spl6_11)),
% 0.21/0.49    inference(superposition,[],[f112,f115])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X1,sK2)) ) | (~spl6_3 | ~spl6_10)),
% 0.21/0.49    inference(subsumption_resolution,[],[f110,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X1,sK2) | ~v1_relat_1(sK3)) ) | ~spl6_10),
% 0.21/0.49    inference(superposition,[],[f36,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    sK3 = k5_relat_1(sK3,k6_relat_1(sK2)) | ~spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | r2_hidden(X1,X2) | ~v1_relat_1(X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_relat_1)).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl6_12 | ~spl6_1 | ~spl6_3 | ~spl6_9 | ~spl6_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f122,f114,f100,f62,f48,f124])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl6_9 <=> sK3 = k5_relat_1(k6_relat_1(sK1),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    r2_hidden(sK4(sK0),sK1) | (~spl6_1 | ~spl6_3 | ~spl6_9 | ~spl6_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f121,f49])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK3) | r2_hidden(sK4(sK0),sK1) | (~spl6_3 | ~spl6_9 | ~spl6_11)),
% 0.21/0.49    inference(superposition,[],[f109,f115])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,sK1)) ) | (~spl6_3 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f107,f63])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,sK1) | ~v1_relat_1(sK3)) ) | ~spl6_9),
% 0.21/0.49    inference(superposition,[],[f33,f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    sK3 = k5_relat_1(k6_relat_1(sK1),sK3) | ~spl6_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) | r2_hidden(X0,X2) | ~v1_relat_1(X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl6_11 | ~spl6_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f96,f93,f114])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl6_8 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    sK0 = k4_tarski(sK4(sK0),sK5(sK0)) | ~spl6_8),
% 0.21/0.49    inference(resolution,[],[f94,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK4(X0),sK5(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl6_10 | ~spl6_3 | ~spl6_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f83,f62,f104])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl6_7 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    sK3 = k5_relat_1(sK3,k6_relat_1(sK2)) | (~spl6_3 | ~spl6_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f63])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | sK3 = k5_relat_1(sK3,k6_relat_1(sK2)) | ~spl6_7),
% 0.21/0.49    inference(resolution,[],[f84,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK3),sK2) | ~spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl6_9 | ~spl6_3 | ~spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f88,f79,f62,f100])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl6_6 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    sK3 = k5_relat_1(k6_relat_1(sK1),sK3) | (~spl6_3 | ~spl6_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f63])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | sK3 = k5_relat_1(k6_relat_1(sK1),sK3) | ~spl6_6),
% 0.21/0.49    inference(resolution,[],[f80,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK3),sK1) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl6_8 | ~spl6_1 | ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f77,f54,f48,f93])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl6_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | (~spl6_1 | ~spl6_2)),
% 0.21/0.49    inference(resolution,[],[f60,f49])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK3) | r2_hidden(X0,k2_zfmisc_1(sK1,sK2))) ) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f55,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl6_7 | ~spl6_3 | ~spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f76,f70,f62,f83])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl6_5 <=> v5_relat_1(sK3,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK3),sK2) | (~spl6_3 | ~spl6_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f75,f63])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | ~spl6_5),
% 0.21/0.49    inference(resolution,[],[f71,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    v5_relat_1(sK3,sK2) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl6_6 | ~spl6_3 | ~spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f74,f66,f62,f79])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl6_4 <=> v4_relat_1(sK3,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK3),sK1) | (~spl6_3 | ~spl6_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f73,f63])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl6_4),
% 0.21/0.49    inference(resolution,[],[f67,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  % (8355)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    v4_relat_1(sK3,sK1) | ~spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl6_5 | ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f59,f54,f70])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v5_relat_1(sK3,sK2) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f55,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl6_4 | ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f54,f66])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    v4_relat_1(sK3,sK1) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f55,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl6_3 | ~spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f54,f62])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f55,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f54])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f48])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    r2_hidden(sK0,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (8349)------------------------------
% 0.21/0.49  % (8349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8349)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (8349)Memory used [KB]: 6268
% 0.21/0.49  % (8349)Time elapsed: 0.067 s
% 0.21/0.49  % (8349)------------------------------
% 0.21/0.49  % (8349)------------------------------
% 0.21/0.49  % (8347)Success in time 0.127 s
%------------------------------------------------------------------------------
