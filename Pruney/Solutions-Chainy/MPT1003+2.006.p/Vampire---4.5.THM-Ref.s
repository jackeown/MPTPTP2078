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
% DateTime   : Thu Dec  3 13:03:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 166 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 ( 459 expanded)
%              Number of equality atoms :   41 ( 113 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f405,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f68,f73,f126,f216,f220,f236,f258,f283,f284,f329,f365,f404])).

fof(f404,plain,
    ( ~ spl5_15
    | ~ spl5_36
    | spl5_41 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | ~ spl5_15
    | ~ spl5_36
    | spl5_41 ),
    inference(trivial_inequality_removal,[],[f402])).

fof(f402,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_15
    | ~ spl5_36
    | spl5_41 ),
    inference(superposition,[],[f364,f388])).

fof(f388,plain,
    ( ! [X0] : k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)
    | ~ spl5_15
    | ~ spl5_36 ),
    inference(resolution,[],[f386,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl5_15 ),
    inference(resolution,[],[f139,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f139,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl5_15 ),
    inference(resolution,[],[f125,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP4(X1) ) ),
    inference(general_splitting,[],[f31,f38_D])).

fof(f38,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP4(X1) ) ),
    inference(cnf_transformation,[],[f38_D])).

fof(f38_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP4(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f125,plain,
    ( sP4(k1_xboole_0)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_15
  <=> sP4(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f386,plain,
    ( ! [X1] : r1_tarski(k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X1),k1_xboole_0)
    | ~ spl5_36 ),
    inference(resolution,[],[f338,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f338,plain,
    ( ! [X2] : m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_36 ),
    inference(resolution,[],[f328,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f328,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl5_36
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f364,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k7_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0))
    | spl5_41 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl5_41
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k7_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f365,plain,
    ( ~ spl5_41
    | ~ spl5_6
    | spl5_21 ),
    inference(avatar_split_clause,[],[f360,f170,f65,f362])).

fof(f65,plain,
    ( spl5_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f170,plain,
    ( spl5_21
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f360,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k7_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0))
    | ~ spl5_6
    | spl5_21 ),
    inference(forward_demodulation,[],[f172,f66])).

fof(f66,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f172,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f170])).

fof(f329,plain,
    ( spl5_36
    | ~ spl5_6
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f324,f185,f65,f326])).

fof(f185,plain,
    ( spl5_24
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f324,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f187,f66])).

fof(f187,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f185])).

fof(f284,plain,
    ( spl5_24
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f273,f61,f46,f185])).

fof(f46,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f61,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f273,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f48,f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f283,plain,
    ( ~ spl5_21
    | spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f272,f61,f41,f170])).

fof(f41,plain,
    ( spl5_1
  <=> sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f272,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0))
    | spl5_1
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f43,f63])).

fof(f43,plain,
    ( sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f258,plain,
    ( spl5_17
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f254,f161,f134])).

fof(f134,plain,
    ( spl5_17
  <=> r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

% (3014)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f161,plain,
    ( spl5_20
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f254,plain,
    ( r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)))
    | ~ spl5_20 ),
    inference(resolution,[],[f162,f35])).

fof(f35,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_tarski(X0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,X0))) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f236,plain,
    ( ~ spl5_2
    | spl5_16 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl5_2
    | spl5_16 ),
    inference(resolution,[],[f224,f132])).

fof(f132,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)),sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_16
  <=> r1_tarski(k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f224,plain,
    ( ! [X1] : r1_tarski(k8_relset_1(sK0,sK1,sK2,X1),sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f140,f30])).

fof(f140,plain,
    ( ! [X0] : m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0),k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f32,f48])).

fof(f220,plain,
    ( ~ spl5_17
    | ~ spl5_16
    | spl5_1 ),
    inference(avatar_split_clause,[],[f218,f41,f130,f134])).

fof(f218,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)),sK0)
    | ~ r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)))
    | spl5_1 ),
    inference(extensionality_resolution,[],[f25,f43])).

fof(f216,plain,
    ( spl5_6
    | spl5_20
    | ~ spl5_4
    | ~ spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f212,f46,f51,f56,f161,f65])).

fof(f56,plain,
    ( spl5_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f51,plain,
    ( spl5_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2)
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK1
        | r1_tarski(X0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,X0))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X1
      | r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

fof(f126,plain,
    ( spl5_15
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f121,f70,f123])).

fof(f70,plain,
    ( spl5_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f121,plain,
    ( sP4(k1_xboole_0)
    | ~ spl5_7 ),
    inference(resolution,[],[f87,f72])).

fof(f72,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sP4(X0) ) ),
    inference(resolution,[],[f38,f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f29,f35])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f22,f70])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f68,plain,
    ( spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f17,f65,f61])).

fof(f17,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

fof(f59,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f18,f56])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f19,f51])).

fof(f19,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (3024)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (3009)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (3017)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (3008)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (3010)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (3016)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (3010)Refutation not found, incomplete strategy% (3010)------------------------------
% 0.20/0.54  % (3010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3010)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3010)Memory used [KB]: 10746
% 0.20/0.54  % (3010)Time elapsed: 0.111 s
% 0.20/0.54  % (3010)------------------------------
% 0.20/0.54  % (3010)------------------------------
% 0.20/0.55  % (3024)Refutation not found, incomplete strategy% (3024)------------------------------
% 0.20/0.55  % (3024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (3018)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (3027)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (3025)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (3026)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (3018)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f405,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f68,f73,f126,f216,f220,f236,f258,f283,f284,f329,f365,f404])).
% 0.20/0.56  fof(f404,plain,(
% 0.20/0.56    ~spl5_15 | ~spl5_36 | spl5_41),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f403])).
% 0.20/0.56  fof(f403,plain,(
% 0.20/0.56    $false | (~spl5_15 | ~spl5_36 | spl5_41)),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f402])).
% 0.20/0.56  fof(f402,plain,(
% 0.20/0.56    k1_xboole_0 != k1_xboole_0 | (~spl5_15 | ~spl5_36 | spl5_41)),
% 0.20/0.56    inference(superposition,[],[f364,f388])).
% 0.20/0.56  fof(f388,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)) ) | (~spl5_15 | ~spl5_36)),
% 0.20/0.56    inference(resolution,[],[f386,f142])).
% 0.20/0.56  fof(f142,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl5_15),
% 0.20/0.56    inference(resolution,[],[f139,f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.56  fof(f139,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl5_15),
% 0.20/0.56    inference(resolution,[],[f125,f82])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~sP4(X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(resolution,[],[f27,f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP4(X1)) )),
% 0.20/0.56    inference(general_splitting,[],[f31,f38_D])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP4(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f38_D])).
% 0.20/0.56  fof(f38_D,plain,(
% 0.20/0.56    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP4(X1)) )),
% 0.20/0.56    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f125,plain,(
% 0.20/0.56    sP4(k1_xboole_0) | ~spl5_15),
% 0.20/0.56    inference(avatar_component_clause,[],[f123])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    spl5_15 <=> sP4(k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.56  fof(f386,plain,(
% 0.20/0.56    ( ! [X1] : (r1_tarski(k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X1),k1_xboole_0)) ) | ~spl5_36),
% 0.20/0.56    inference(resolution,[],[f338,f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.56  fof(f338,plain,(
% 0.20/0.56    ( ! [X2] : (m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X2),k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_36),
% 0.20/0.56    inference(resolution,[],[f328,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.20/0.56  fof(f328,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_36),
% 0.20/0.56    inference(avatar_component_clause,[],[f326])).
% 0.20/0.56  fof(f326,plain,(
% 0.20/0.56    spl5_36 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.20/0.56  fof(f364,plain,(
% 0.20/0.56    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k7_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)) | spl5_41),
% 0.20/0.56    inference(avatar_component_clause,[],[f362])).
% 0.20/0.56  fof(f362,plain,(
% 0.20/0.56    spl5_41 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k7_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.20/0.56  fof(f365,plain,(
% 0.20/0.56    ~spl5_41 | ~spl5_6 | spl5_21),
% 0.20/0.56    inference(avatar_split_clause,[],[f360,f170,f65,f362])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    spl5_6 <=> k1_xboole_0 = sK1),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.56  fof(f170,plain,(
% 0.20/0.56    spl5_21 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.56  fof(f360,plain,(
% 0.20/0.56    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k7_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)) | (~spl5_6 | spl5_21)),
% 0.20/0.56    inference(forward_demodulation,[],[f172,f66])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    k1_xboole_0 = sK1 | ~spl5_6),
% 0.20/0.56    inference(avatar_component_clause,[],[f65])).
% 0.20/0.56  fof(f172,plain,(
% 0.20/0.56    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0)) | spl5_21),
% 0.20/0.56    inference(avatar_component_clause,[],[f170])).
% 0.20/0.56  fof(f329,plain,(
% 0.20/0.56    spl5_36 | ~spl5_6 | ~spl5_24),
% 0.20/0.56    inference(avatar_split_clause,[],[f324,f185,f65,f326])).
% 0.20/0.56  fof(f185,plain,(
% 0.20/0.56    spl5_24 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.56  fof(f324,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_6 | ~spl5_24)),
% 0.20/0.56    inference(forward_demodulation,[],[f187,f66])).
% 0.20/0.56  fof(f187,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_24),
% 0.20/0.56    inference(avatar_component_clause,[],[f185])).
% 0.20/0.56  fof(f284,plain,(
% 0.20/0.56    spl5_24 | ~spl5_2 | ~spl5_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f273,f61,f46,f185])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    spl5_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    spl5_5 <=> k1_xboole_0 = sK0),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.56  fof(f273,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_2 | ~spl5_5)),
% 0.20/0.56    inference(backward_demodulation,[],[f48,f63])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    k1_xboole_0 = sK0 | ~spl5_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f61])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f46])).
% 0.20/0.56  fof(f283,plain,(
% 0.20/0.56    ~spl5_21 | spl5_1 | ~spl5_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f272,f61,f41,f170])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    spl5_1 <=> sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.56  fof(f272,plain,(
% 0.20/0.56    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0)) | (spl5_1 | ~spl5_5)),
% 0.20/0.56    inference(backward_demodulation,[],[f43,f63])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) | spl5_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f41])).
% 0.20/0.56  fof(f258,plain,(
% 0.20/0.56    spl5_17 | ~spl5_20),
% 0.20/0.56    inference(avatar_split_clause,[],[f254,f161,f134])).
% 0.20/0.56  fof(f134,plain,(
% 0.20/0.56    spl5_17 <=> r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.56  % (3014)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  fof(f161,plain,(
% 0.20/0.56    spl5_20 <=> ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,X0))))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.56  fof(f254,plain,(
% 0.20/0.56    r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))) | ~spl5_20),
% 0.20/0.56    inference(resolution,[],[f162,f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f162,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_tarski(X0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,X0)))) ) | ~spl5_20),
% 0.20/0.56    inference(avatar_component_clause,[],[f161])).
% 0.20/0.56  fof(f236,plain,(
% 0.20/0.56    ~spl5_2 | spl5_16),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f233])).
% 0.20/0.56  fof(f233,plain,(
% 0.20/0.56    $false | (~spl5_2 | spl5_16)),
% 0.20/0.56    inference(resolution,[],[f224,f132])).
% 0.20/0.56  fof(f132,plain,(
% 0.20/0.56    ~r1_tarski(k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)),sK0) | spl5_16),
% 0.20/0.56    inference(avatar_component_clause,[],[f130])).
% 0.20/0.56  fof(f130,plain,(
% 0.20/0.56    spl5_16 <=> r1_tarski(k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)),sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.56  fof(f224,plain,(
% 0.20/0.56    ( ! [X1] : (r1_tarski(k8_relset_1(sK0,sK1,sK2,X1),sK0)) ) | ~spl5_2),
% 0.20/0.56    inference(resolution,[],[f140,f30])).
% 0.20/0.56  fof(f140,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0),k1_zfmisc_1(sK0))) ) | ~spl5_2),
% 0.20/0.56    inference(resolution,[],[f32,f48])).
% 0.20/0.56  fof(f220,plain,(
% 0.20/0.56    ~spl5_17 | ~spl5_16 | spl5_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f218,f41,f130,f134])).
% 0.20/0.56  fof(f218,plain,(
% 0.20/0.56    ~r1_tarski(k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)),sK0) | ~r1_tarski(sK0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))) | spl5_1),
% 0.20/0.56    inference(extensionality_resolution,[],[f25,f43])).
% 0.20/0.56  fof(f216,plain,(
% 0.20/0.56    spl5_6 | spl5_20 | ~spl5_4 | ~spl5_3 | ~spl5_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f212,f46,f51,f56,f161,f65])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    spl5_4 <=> v1_funct_1(sK2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    spl5_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.56  fof(f212,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~r1_tarski(X0,sK0) | k1_xboole_0 = sK1 | r1_tarski(X0,k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,X0)))) ) | ~spl5_2),
% 0.20/0.56    inference(resolution,[],[f48,f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(X2,X0) | k1_xboole_0 = X1 | r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.56    inference(flattening,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).
% 0.20/0.56  fof(f126,plain,(
% 0.20/0.56    spl5_15 | ~spl5_7),
% 0.20/0.56    inference(avatar_split_clause,[],[f121,f70,f123])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    spl5_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.56  fof(f121,plain,(
% 0.20/0.56    sP4(k1_xboole_0) | ~spl5_7),
% 0.20/0.56    inference(resolution,[],[f87,f72])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0) | ~spl5_7),
% 0.20/0.56    inference(avatar_component_clause,[],[f70])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_xboole_0(X0) | sP4(X0)) )),
% 0.20/0.56    inference(resolution,[],[f38,f74])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.56    inference(resolution,[],[f29,f35])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    spl5_7),
% 0.20/0.56    inference(avatar_split_clause,[],[f22,f70])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    inference(cnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    v1_xboole_0(k1_xboole_0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    spl5_5 | ~spl5_6),
% 0.20/0.56    inference(avatar_split_clause,[],[f17,f65,f61])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.56    inference(flattening,[],[f10])).
% 0.20/0.56  fof(f10,plain,(
% 0.20/0.56    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.20/0.56    inference(negated_conjecture,[],[f8])).
% 0.20/0.56  fof(f8,conjecture,(
% 0.20/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    spl5_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f18,f56])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    v1_funct_1(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    spl5_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f19,f51])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    spl5_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f20,f46])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ~spl5_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f21,f41])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (3018)------------------------------
% 0.20/0.56  % (3018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (3018)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (3018)Memory used [KB]: 11001
% 0.20/0.56  % (3018)Time elapsed: 0.135 s
% 0.20/0.56  % (3018)------------------------------
% 0.20/0.56  % (3018)------------------------------
% 0.20/0.56  % (3024)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (3024)Memory used [KB]: 10746
% 0.20/0.56  % (3024)Time elapsed: 0.114 s
% 0.20/0.56  % (3024)------------------------------
% 0.20/0.56  % (3024)------------------------------
% 0.20/0.56  % (3004)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.57  % (3005)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.57  % (3001)Success in time 0.201 s
%------------------------------------------------------------------------------
