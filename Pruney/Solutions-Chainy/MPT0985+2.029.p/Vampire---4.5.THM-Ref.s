%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 521 expanded)
%              Number of leaves         :   33 ( 156 expanded)
%              Depth                    :   14
%              Number of atoms          :  634 (2532 expanded)
%              Number of equality atoms :  122 ( 471 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f564,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f103,f120,f133,f139,f153,f240,f301,f310,f373,f375,f378,f431,f512,f526,f535,f544,f554,f563])).

fof(f563,plain,
    ( spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f541,f534])).

fof(f534,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f532])).

fof(f532,plain,
    ( spl5_27
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f541,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f540,f405])).

fof(f405,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f143,f193])).

fof(f193,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl5_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f143,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl5_9
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f540,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl5_2
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f539,f193])).

fof(f539,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl5_2
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f90,f196])).

fof(f196,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl5_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f90,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f554,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | spl5_23
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | ~ spl5_11
    | ~ spl5_12
    | spl5_23
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f550,f529])).

fof(f529,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl5_26
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f550,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl5_11
    | ~ spl5_12
    | spl5_23 ),
    inference(subsumption_resolution,[],[f546,f432])).

fof(f432,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f171,f193])).

fof(f171,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_11
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f546,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl5_23 ),
    inference(superposition,[],[f467,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f467,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl5_23
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f544,plain,
    ( ~ spl5_22
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f543])).

fof(f543,plain,
    ( $false
    | ~ spl5_22
    | spl5_26 ),
    inference(subsumption_resolution,[],[f542,f463])).

fof(f463,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl5_22
  <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f542,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0))
    | spl5_26 ),
    inference(resolution,[],[f530,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f530,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f528])).

fof(f535,plain,
    ( ~ spl5_26
    | spl5_27
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f516,f466,f532,f528])).

fof(f516,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl5_23 ),
    inference(trivial_inequality_removal,[],[f514])).

fof(f514,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl5_23 ),
    inference(superposition,[],[f81,f468])).

fof(f468,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f466])).

fof(f81,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f526,plain,
    ( spl5_3
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | spl5_3
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f480,f463])).

fof(f480,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0))
    | spl5_3
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f479,f405])).

fof(f479,plain,
    ( ~ r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0))
    | spl5_3
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f399,f196])).

fof(f399,plain,
    ( ~ r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(sK1,sK0))
    | spl5_3
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f359,f193])).

fof(f359,plain,
    ( ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0))
    | spl5_3 ),
    inference(resolution,[],[f94,f68])).

fof(f94,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f512,plain,(
    spl5_22 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | spl5_22 ),
    inference(subsumption_resolution,[],[f510,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f510,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_22 ),
    inference(resolution,[],[f470,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

% (26711)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (26715)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (26719)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (26716)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (26709)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (26723)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (26722)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (26720)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (26717)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (26710)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (26713)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (26702)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (26699)Refutation not found, incomplete strategy% (26699)------------------------------
% (26699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26699)Termination reason: Refutation not found, incomplete strategy

% (26699)Memory used [KB]: 6396
% (26699)Time elapsed: 0.129 s
% (26699)------------------------------
% (26699)------------------------------
fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f470,plain,
    ( r2_hidden(sK4(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)),k1_xboole_0)
    | spl5_22 ),
    inference(resolution,[],[f464,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f464,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f462])).

fof(f431,plain,
    ( ~ spl5_4
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_9
    | spl5_11
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f429,f268])).

fof(f268,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl5_11
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f172,f193])).

fof(f172,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f170])).

fof(f429,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f428,f404])).

fof(f404,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f397,f196])).

fof(f397,plain,
    ( sK1 = k2_relat_1(k1_xboole_0)
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f176,f193])).

fof(f176,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f174,f47])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f174,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f71,f49])).

fof(f49,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f428,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f427,f405])).

fof(f427,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f156,f193])).

fof(f156,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f155,f109])).

fof(f109,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f155,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f154,f45])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f154,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f61,f48])).

fof(f48,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f378,plain,
    ( spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f377,f249,f195])).

fof(f249,plain,
    ( spl5_14
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f377,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f333,f46])).

fof(f46,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f333,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f47,f220])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f70,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f375,plain,
    ( spl5_9
    | ~ spl5_13
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f374,f126,f112,f195,f141])).

fof(f112,plain,
    ( spl5_5
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f126,plain,
    ( spl5_6
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f374,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f339,f127])).

fof(f127,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f339,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_5 ),
    inference(superposition,[],[f53,f180])).

fof(f180,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f114,f176])).

fof(f114,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f373,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f371,f94])).

fof(f371,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f178,f251])).

fof(f251,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f249])).

fof(f178,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f157,f176])).

fof(f157,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f132,f156])).

fof(f132,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_7
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f310,plain,
    ( spl5_12
    | ~ spl5_13
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f309,f108,f195,f191])).

fof(f309,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f304,f109])).

fof(f304,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f54,f176])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f301,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f300,f112,f108])).

fof(f300,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f293,f45])).

fof(f293,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f240,plain,
    ( spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl5_2
    | ~ spl5_4
    | ~ spl5_8
    | spl5_13 ),
    inference(subsumption_resolution,[],[f231,f90])).

fof(f231,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl5_4
    | ~ spl5_8
    | spl5_13 ),
    inference(backward_demodulation,[],[f179,f228])).

fof(f228,plain,
    ( sK0 = k1_relat_1(sK2)
    | spl5_13 ),
    inference(subsumption_resolution,[],[f227,f197])).

fof(f197,plain,
    ( k1_xboole_0 != sK1
    | spl5_13 ),
    inference(avatar_component_clause,[],[f195])).

fof(f227,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f222,f46])).

fof(f222,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f220,f47])).

fof(f179,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f158,f176])).

fof(f158,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f138,f156])).

fof(f138,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_8
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f153,plain,
    ( ~ spl5_4
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl5_4
    | spl5_6 ),
    inference(subsumption_resolution,[],[f151,f109])).

fof(f151,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_6 ),
    inference(subsumption_resolution,[],[f149,f45])).

fof(f149,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_6 ),
    inference(resolution,[],[f128,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f128,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f139,plain,
    ( ~ spl5_6
    | spl5_8
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f134,f112,f84,f136,f126])).

fof(f84,plain,
    ( spl5_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f134,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f122,f85])).

fof(f85,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f122,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_5 ),
    inference(superposition,[],[f56,f114])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f133,plain,
    ( ~ spl5_6
    | spl5_7
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f124,f112,f84,f130,f126])).

fof(f124,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f121,f85])).

fof(f121,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_5 ),
    inference(superposition,[],[f57,f114])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f116,f47])).

fof(f116,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_4 ),
    inference(resolution,[],[f110,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f110,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f103,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl5_1 ),
    inference(resolution,[],[f100,f47])).

fof(f100,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_1 ),
    inference(resolution,[],[f69,f99])).

fof(f99,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f98,f45])).

fof(f98,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1 ),
    inference(resolution,[],[f59,f86])).

fof(f86,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f95,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f50,f92,f88,f84])).

fof(f50,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (26696)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (26698)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (26704)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (26706)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (26707)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (26697)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (26721)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (26708)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (26718)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (26700)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (26714)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (26705)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (26701)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (26699)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (26695)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (26698)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f564,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f95,f103,f120,f133,f139,f153,f240,f301,f310,f373,f375,f378,f431,f512,f526,f535,f544,f554,f563])).
% 0.20/0.54  fof(f563,plain,(
% 0.20/0.54    spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_27),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f562])).
% 0.20/0.54  fof(f562,plain,(
% 0.20/0.54    $false | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_27)),
% 0.20/0.54    inference(subsumption_resolution,[],[f541,f534])).
% 0.20/0.54  fof(f534,plain,(
% 0.20/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | ~spl5_27),
% 0.20/0.54    inference(avatar_component_clause,[],[f532])).
% 0.20/0.54  fof(f532,plain,(
% 0.20/0.54    spl5_27 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.20/0.54  fof(f541,plain,(
% 0.20/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl5_2 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 0.20/0.54    inference(forward_demodulation,[],[f540,f405])).
% 0.20/0.54  fof(f405,plain,(
% 0.20/0.54    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl5_9 | ~spl5_12)),
% 0.20/0.54    inference(forward_demodulation,[],[f143,f193])).
% 0.20/0.54  fof(f193,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | ~spl5_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f191])).
% 0.20/0.54  fof(f191,plain,(
% 0.20/0.54    spl5_12 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    k1_xboole_0 = k2_funct_1(sK2) | ~spl5_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f141])).
% 0.20/0.54  fof(f141,plain,(
% 0.20/0.54    spl5_9 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.54  fof(f540,plain,(
% 0.20/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl5_2 | ~spl5_12 | ~spl5_13)),
% 0.20/0.54    inference(forward_demodulation,[],[f539,f193])).
% 0.20/0.54  fof(f539,plain,(
% 0.20/0.54    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl5_2 | ~spl5_13)),
% 0.20/0.54    inference(forward_demodulation,[],[f90,f196])).
% 0.20/0.54  fof(f196,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | ~spl5_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f195])).
% 0.20/0.54  fof(f195,plain,(
% 0.20/0.54    spl5_13 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl5_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f88])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    spl5_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.54  fof(f554,plain,(
% 0.20/0.54    ~spl5_11 | ~spl5_12 | spl5_23 | ~spl5_26),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f553])).
% 0.20/0.54  fof(f553,plain,(
% 0.20/0.54    $false | (~spl5_11 | ~spl5_12 | spl5_23 | ~spl5_26)),
% 0.20/0.54    inference(subsumption_resolution,[],[f550,f529])).
% 0.20/0.54  fof(f529,plain,(
% 0.20/0.54    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl5_26),
% 0.20/0.54    inference(avatar_component_clause,[],[f528])).
% 0.20/0.54  fof(f528,plain,(
% 0.20/0.54    spl5_26 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.20/0.54  fof(f550,plain,(
% 0.20/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl5_11 | ~spl5_12 | spl5_23)),
% 0.20/0.54    inference(subsumption_resolution,[],[f546,f432])).
% 0.20/0.54  fof(f432,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_11 | ~spl5_12)),
% 0.20/0.54    inference(forward_demodulation,[],[f171,f193])).
% 0.20/0.54  fof(f171,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f170])).
% 0.20/0.54  fof(f170,plain,(
% 0.20/0.54    spl5_11 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.54  fof(f546,plain,(
% 0.20/0.54    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl5_23),
% 0.20/0.54    inference(superposition,[],[f467,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.54  fof(f467,plain,(
% 0.20/0.54    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | spl5_23),
% 0.20/0.54    inference(avatar_component_clause,[],[f466])).
% 0.20/0.54  fof(f466,plain,(
% 0.20/0.54    spl5_23 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.54  fof(f544,plain,(
% 0.20/0.54    ~spl5_22 | spl5_26),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f543])).
% 0.20/0.54  fof(f543,plain,(
% 0.20/0.54    $false | (~spl5_22 | spl5_26)),
% 0.20/0.54    inference(subsumption_resolution,[],[f542,f463])).
% 0.20/0.54  fof(f463,plain,(
% 0.20/0.54    r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)) | ~spl5_22),
% 0.20/0.54    inference(avatar_component_clause,[],[f462])).
% 0.20/0.54  fof(f462,plain,(
% 0.20/0.54    spl5_22 <=> r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.54  fof(f542,plain,(
% 0.20/0.54    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)) | spl5_26),
% 0.20/0.54    inference(resolution,[],[f530,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f530,plain,(
% 0.20/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl5_26),
% 0.20/0.54    inference(avatar_component_clause,[],[f528])).
% 0.20/0.54  fof(f535,plain,(
% 0.20/0.54    ~spl5_26 | spl5_27 | ~spl5_23),
% 0.20/0.54    inference(avatar_split_clause,[],[f516,f466,f532,f528])).
% 0.20/0.54  fof(f516,plain,(
% 0.20/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl5_23),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f514])).
% 0.20/0.54  fof(f514,plain,(
% 0.20/0.54    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl5_23),
% 0.20/0.54    inference(superposition,[],[f81,f468])).
% 0.20/0.54  fof(f468,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) | ~spl5_23),
% 0.20/0.54    inference(avatar_component_clause,[],[f466])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.54    inference(equality_resolution,[],[f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.54  fof(f526,plain,(
% 0.20/0.54    spl5_3 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_22),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f525])).
% 0.20/0.54  fof(f525,plain,(
% 0.20/0.54    $false | (spl5_3 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_22)),
% 0.20/0.54    inference(subsumption_resolution,[],[f480,f463])).
% 0.20/0.54  fof(f480,plain,(
% 0.20/0.54    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)) | (spl5_3 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 0.20/0.54    inference(forward_demodulation,[],[f479,f405])).
% 0.20/0.54  fof(f479,plain,(
% 0.20/0.54    ~r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,sK0)) | (spl5_3 | ~spl5_12 | ~spl5_13)),
% 0.20/0.54    inference(forward_demodulation,[],[f399,f196])).
% 0.20/0.54  fof(f399,plain,(
% 0.20/0.54    ~r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(sK1,sK0)) | (spl5_3 | ~spl5_12)),
% 0.20/0.54    inference(backward_demodulation,[],[f359,f193])).
% 0.20/0.54  fof(f359,plain,(
% 0.20/0.54    ~r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) | spl5_3),
% 0.20/0.54    inference(resolution,[],[f94,f68])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f92])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    spl5_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.54  fof(f512,plain,(
% 0.20/0.54    spl5_22),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f511])).
% 0.20/0.54  fof(f511,plain,(
% 0.20/0.54    $false | spl5_22),
% 0.20/0.54    inference(subsumption_resolution,[],[f510,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0)),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.54  fof(f510,plain,(
% 0.20/0.54    ~v1_xboole_0(k1_xboole_0) | spl5_22),
% 0.20/0.54    inference(resolution,[],[f470,f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f38])).
% 0.20/0.54  % (26711)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (26715)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.54  % (26719)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.55  % (26716)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.55  % (26709)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.44/0.55  % (26723)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.55  % (26722)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.55  % (26720)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.55  % (26717)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.44/0.56  % (26710)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.44/0.56  % (26713)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.56  % (26702)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.57/0.57  % (26699)Refutation not found, incomplete strategy% (26699)------------------------------
% 1.57/0.57  % (26699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (26699)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (26699)Memory used [KB]: 6396
% 1.57/0.57  % (26699)Time elapsed: 0.129 s
% 1.57/0.57  % (26699)------------------------------
% 1.57/0.57  % (26699)------------------------------
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f36,plain,(
% 1.57/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.57    inference(rectify,[],[f35])).
% 1.57/0.57  fof(f35,plain,(
% 1.57/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.57    inference(nnf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.57/0.57  fof(f470,plain,(
% 1.57/0.57    r2_hidden(sK4(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)),k1_xboole_0) | spl5_22),
% 1.57/0.57    inference(resolution,[],[f464,f65])).
% 1.57/0.57  fof(f65,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f42])).
% 1.57/0.57  fof(f42,plain,(
% 1.57/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.57/0.57  fof(f41,plain,(
% 1.57/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.57    inference(rectify,[],[f39])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.57/0.57    inference(nnf_transformation,[],[f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.57  fof(f464,plain,(
% 1.57/0.57    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,sK0)) | spl5_22),
% 1.57/0.57    inference(avatar_component_clause,[],[f462])).
% 1.57/0.57  fof(f431,plain,(
% 1.57/0.57    ~spl5_4 | ~spl5_9 | spl5_11 | ~spl5_12 | ~spl5_13),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f430])).
% 1.57/0.57  fof(f430,plain,(
% 1.57/0.57    $false | (~spl5_4 | ~spl5_9 | spl5_11 | ~spl5_12 | ~spl5_13)),
% 1.57/0.57    inference(subsumption_resolution,[],[f429,f268])).
% 1.57/0.57  fof(f268,plain,(
% 1.57/0.57    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (spl5_11 | ~spl5_12)),
% 1.57/0.57    inference(backward_demodulation,[],[f172,f193])).
% 1.57/0.57  fof(f172,plain,(
% 1.57/0.57    k1_xboole_0 != k1_relat_1(sK2) | spl5_11),
% 1.57/0.57    inference(avatar_component_clause,[],[f170])).
% 1.57/0.57  fof(f429,plain,(
% 1.57/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_4 | ~spl5_9 | ~spl5_12 | ~spl5_13)),
% 1.57/0.57    inference(forward_demodulation,[],[f428,f404])).
% 1.57/0.57  fof(f404,plain,(
% 1.57/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl5_12 | ~spl5_13)),
% 1.57/0.57    inference(forward_demodulation,[],[f397,f196])).
% 1.57/0.57  fof(f397,plain,(
% 1.57/0.57    sK1 = k2_relat_1(k1_xboole_0) | ~spl5_12),
% 1.57/0.57    inference(backward_demodulation,[],[f176,f193])).
% 1.57/0.57  fof(f176,plain,(
% 1.57/0.57    sK1 = k2_relat_1(sK2)),
% 1.57/0.57    inference(subsumption_resolution,[],[f174,f47])).
% 1.57/0.57  fof(f47,plain,(
% 1.57/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.57/0.57    inference(cnf_transformation,[],[f34])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f17,plain,(
% 1.57/0.57    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.57/0.57    inference(flattening,[],[f16])).
% 1.57/0.57  fof(f16,plain,(
% 1.57/0.57    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.57/0.57    inference(ennf_transformation,[],[f15])).
% 1.57/0.57  fof(f15,negated_conjecture,(
% 1.57/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.57/0.57    inference(negated_conjecture,[],[f14])).
% 1.57/0.57  fof(f14,conjecture,(
% 1.57/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.57/0.57  fof(f174,plain,(
% 1.57/0.57    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.57/0.57    inference(superposition,[],[f71,f49])).
% 1.57/0.57  fof(f49,plain,(
% 1.57/0.57    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.57/0.57    inference(cnf_transformation,[],[f34])).
% 1.57/0.57  fof(f71,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f30])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.57/0.57  fof(f428,plain,(
% 1.57/0.57    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) | (~spl5_4 | ~spl5_9 | ~spl5_12)),
% 1.57/0.57    inference(forward_demodulation,[],[f427,f405])).
% 1.57/0.57  fof(f427,plain,(
% 1.57/0.57    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl5_4 | ~spl5_12)),
% 1.57/0.57    inference(forward_demodulation,[],[f156,f193])).
% 1.57/0.57  fof(f156,plain,(
% 1.57/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_4),
% 1.57/0.57    inference(subsumption_resolution,[],[f155,f109])).
% 1.57/0.57  fof(f109,plain,(
% 1.57/0.57    v1_relat_1(sK2) | ~spl5_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f108])).
% 1.57/0.57  fof(f108,plain,(
% 1.57/0.57    spl5_4 <=> v1_relat_1(sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.57/0.57  fof(f155,plain,(
% 1.57/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.57/0.57    inference(subsumption_resolution,[],[f154,f45])).
% 1.57/0.57  fof(f45,plain,(
% 1.57/0.57    v1_funct_1(sK2)),
% 1.57/0.57    inference(cnf_transformation,[],[f34])).
% 1.57/0.57  fof(f154,plain,(
% 1.57/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.57/0.57    inference(resolution,[],[f61,f48])).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    v2_funct_1(sK2)),
% 1.57/0.57    inference(cnf_transformation,[],[f34])).
% 1.57/0.57  fof(f61,plain,(
% 1.57/0.57    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.57/0.57  fof(f378,plain,(
% 1.57/0.57    spl5_13 | spl5_14),
% 1.57/0.57    inference(avatar_split_clause,[],[f377,f249,f195])).
% 1.57/0.57  fof(f249,plain,(
% 1.57/0.57    spl5_14 <=> sK0 = k1_relat_1(sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.57/0.57  fof(f377,plain,(
% 1.57/0.57    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.57/0.57    inference(subsumption_resolution,[],[f333,f46])).
% 1.57/0.57  fof(f46,plain,(
% 1.57/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f34])).
% 1.57/0.57  fof(f333,plain,(
% 1.57/0.57    sK0 = k1_relat_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1),
% 1.57/0.57    inference(resolution,[],[f47,f220])).
% 1.57/0.57  fof(f220,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1) )),
% 1.57/0.57    inference(duplicate_literal_removal,[],[f217])).
% 1.57/0.57  fof(f217,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k1_relat_1(X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.57    inference(superposition,[],[f70,f72])).
% 1.57/0.57  fof(f72,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f44])).
% 1.57/0.57  fof(f375,plain,(
% 1.57/0.57    spl5_9 | ~spl5_13 | ~spl5_5 | ~spl5_6),
% 1.57/0.57    inference(avatar_split_clause,[],[f374,f126,f112,f195,f141])).
% 1.57/0.57  fof(f112,plain,(
% 1.57/0.57    spl5_5 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.57/0.57  fof(f126,plain,(
% 1.57/0.57    spl5_6 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.57/0.57  fof(f374,plain,(
% 1.57/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = k2_funct_1(sK2) | (~spl5_5 | ~spl5_6)),
% 1.57/0.57    inference(subsumption_resolution,[],[f339,f127])).
% 1.57/0.57  fof(f127,plain,(
% 1.57/0.57    v1_relat_1(k2_funct_1(sK2)) | ~spl5_6),
% 1.57/0.57    inference(avatar_component_clause,[],[f126])).
% 1.57/0.57  fof(f339,plain,(
% 1.57/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl5_5),
% 1.57/0.57    inference(superposition,[],[f53,f180])).
% 1.57/0.57  fof(f180,plain,(
% 1.57/0.57    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl5_5),
% 1.57/0.57    inference(backward_demodulation,[],[f114,f176])).
% 1.57/0.57  fof(f114,plain,(
% 1.57/0.57    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl5_5),
% 1.57/0.57    inference(avatar_component_clause,[],[f112])).
% 1.57/0.57  fof(f53,plain,(
% 1.57/0.57    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f20])).
% 1.57/0.57  fof(f20,plain,(
% 1.57/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f19])).
% 1.57/0.57  fof(f19,plain,(
% 1.57/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.57/0.57  fof(f373,plain,(
% 1.57/0.57    spl5_3 | ~spl5_4 | ~spl5_7 | ~spl5_14),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f372])).
% 1.57/0.57  fof(f372,plain,(
% 1.57/0.57    $false | (spl5_3 | ~spl5_4 | ~spl5_7 | ~spl5_14)),
% 1.57/0.57    inference(subsumption_resolution,[],[f371,f94])).
% 1.57/0.57  fof(f371,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_4 | ~spl5_7 | ~spl5_14)),
% 1.57/0.57    inference(forward_demodulation,[],[f178,f251])).
% 1.57/0.57  fof(f251,plain,(
% 1.57/0.57    sK0 = k1_relat_1(sK2) | ~spl5_14),
% 1.57/0.57    inference(avatar_component_clause,[],[f249])).
% 1.57/0.57  fof(f178,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl5_4 | ~spl5_7)),
% 1.57/0.57    inference(backward_demodulation,[],[f157,f176])).
% 1.57/0.57  fof(f157,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl5_4 | ~spl5_7)),
% 1.57/0.57    inference(backward_demodulation,[],[f132,f156])).
% 1.57/0.57  fof(f132,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~spl5_7),
% 1.57/0.57    inference(avatar_component_clause,[],[f130])).
% 1.57/0.57  fof(f130,plain,(
% 1.57/0.57    spl5_7 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.57/0.57  fof(f310,plain,(
% 1.57/0.57    spl5_12 | ~spl5_13 | ~spl5_4),
% 1.57/0.57    inference(avatar_split_clause,[],[f309,f108,f195,f191])).
% 1.57/0.57  fof(f309,plain,(
% 1.57/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~spl5_4),
% 1.57/0.57    inference(subsumption_resolution,[],[f304,f109])).
% 1.57/0.57  fof(f304,plain,(
% 1.57/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2)),
% 1.57/0.57    inference(superposition,[],[f54,f176])).
% 1.57/0.57  fof(f54,plain,(
% 1.57/0.57    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f20])).
% 1.57/0.57  fof(f301,plain,(
% 1.57/0.57    ~spl5_4 | spl5_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f300,f112,f108])).
% 1.57/0.57  fof(f300,plain,(
% 1.57/0.57    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.57/0.57    inference(subsumption_resolution,[],[f293,f45])).
% 1.57/0.57  fof(f293,plain,(
% 1.57/0.57    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.57/0.57    inference(resolution,[],[f48,f60])).
% 1.57/0.57  fof(f60,plain,(
% 1.57/0.57    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f26])).
% 1.57/0.57  fof(f240,plain,(
% 1.57/0.57    spl5_2 | ~spl5_4 | ~spl5_8 | spl5_13),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f239])).
% 1.57/0.57  fof(f239,plain,(
% 1.57/0.57    $false | (spl5_2 | ~spl5_4 | ~spl5_8 | spl5_13)),
% 1.57/0.57    inference(subsumption_resolution,[],[f231,f90])).
% 1.57/0.57  fof(f231,plain,(
% 1.57/0.57    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl5_4 | ~spl5_8 | spl5_13)),
% 1.57/0.57    inference(backward_demodulation,[],[f179,f228])).
% 1.57/0.57  fof(f228,plain,(
% 1.57/0.57    sK0 = k1_relat_1(sK2) | spl5_13),
% 1.57/0.57    inference(subsumption_resolution,[],[f227,f197])).
% 1.57/0.57  fof(f197,plain,(
% 1.57/0.57    k1_xboole_0 != sK1 | spl5_13),
% 1.57/0.57    inference(avatar_component_clause,[],[f195])).
% 1.57/0.57  fof(f227,plain,(
% 1.57/0.57    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.57/0.57    inference(subsumption_resolution,[],[f222,f46])).
% 1.57/0.57  fof(f222,plain,(
% 1.57/0.57    sK0 = k1_relat_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1),
% 1.57/0.57    inference(resolution,[],[f220,f47])).
% 1.57/0.57  fof(f179,plain,(
% 1.57/0.57    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl5_4 | ~spl5_8)),
% 1.57/0.57    inference(backward_demodulation,[],[f158,f176])).
% 1.57/0.57  fof(f158,plain,(
% 1.57/0.57    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl5_4 | ~spl5_8)),
% 1.57/0.57    inference(backward_demodulation,[],[f138,f156])).
% 1.57/0.57  fof(f138,plain,(
% 1.57/0.57    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~spl5_8),
% 1.57/0.57    inference(avatar_component_clause,[],[f136])).
% 1.57/0.57  fof(f136,plain,(
% 1.57/0.57    spl5_8 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.57/0.57  fof(f153,plain,(
% 1.57/0.57    ~spl5_4 | spl5_6),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f152])).
% 1.57/0.57  fof(f152,plain,(
% 1.57/0.57    $false | (~spl5_4 | spl5_6)),
% 1.57/0.57    inference(subsumption_resolution,[],[f151,f109])).
% 1.57/0.57  fof(f151,plain,(
% 1.57/0.57    ~v1_relat_1(sK2) | spl5_6),
% 1.57/0.57    inference(subsumption_resolution,[],[f149,f45])).
% 1.57/0.57  fof(f149,plain,(
% 1.57/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_6),
% 1.57/0.57    inference(resolution,[],[f128,f58])).
% 1.57/0.57  fof(f58,plain,(
% 1.57/0.57    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f23])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.57/0.57  fof(f128,plain,(
% 1.57/0.57    ~v1_relat_1(k2_funct_1(sK2)) | spl5_6),
% 1.57/0.57    inference(avatar_component_clause,[],[f126])).
% 1.57/0.57  fof(f139,plain,(
% 1.57/0.57    ~spl5_6 | spl5_8 | ~spl5_1 | ~spl5_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f134,f112,f84,f136,f126])).
% 1.57/0.57  fof(f84,plain,(
% 1.57/0.57    spl5_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.57/0.57  fof(f134,plain,(
% 1.57/0.57    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_5)),
% 1.57/0.57    inference(subsumption_resolution,[],[f122,f85])).
% 1.57/0.57  fof(f85,plain,(
% 1.57/0.57    v1_funct_1(k2_funct_1(sK2)) | ~spl5_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f84])).
% 1.57/0.57  fof(f122,plain,(
% 1.57/0.57    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl5_5),
% 1.57/0.57    inference(superposition,[],[f56,f114])).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.57    inference(flattening,[],[f21])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f13])).
% 1.57/0.57  fof(f13,axiom,(
% 1.57/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.57/0.57  fof(f133,plain,(
% 1.57/0.57    ~spl5_6 | spl5_7 | ~spl5_1 | ~spl5_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f124,f112,f84,f130,f126])).
% 1.57/0.57  fof(f124,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_5)),
% 1.57/0.57    inference(subsumption_resolution,[],[f121,f85])).
% 1.57/0.57  fof(f121,plain,(
% 1.57/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl5_5),
% 1.57/0.57    inference(superposition,[],[f57,f114])).
% 1.57/0.57  fof(f57,plain,(
% 1.57/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f22])).
% 1.57/0.57  fof(f120,plain,(
% 1.57/0.57    spl5_4),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f117])).
% 1.57/0.57  fof(f117,plain,(
% 1.57/0.57    $false | spl5_4),
% 1.57/0.57    inference(resolution,[],[f116,f47])).
% 1.57/0.57  fof(f116,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_4),
% 1.57/0.57    inference(resolution,[],[f110,f69])).
% 1.57/0.57  fof(f69,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.57    inference(ennf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.57/0.57  fof(f110,plain,(
% 1.57/0.57    ~v1_relat_1(sK2) | spl5_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f108])).
% 1.57/0.57  fof(f103,plain,(
% 1.57/0.57    spl5_1),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f101])).
% 1.57/0.57  fof(f101,plain,(
% 1.57/0.57    $false | spl5_1),
% 1.57/0.57    inference(resolution,[],[f100,f47])).
% 1.57/0.57  fof(f100,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_1),
% 1.57/0.57    inference(resolution,[],[f69,f99])).
% 1.57/0.57  fof(f99,plain,(
% 1.57/0.57    ~v1_relat_1(sK2) | spl5_1),
% 1.57/0.57    inference(subsumption_resolution,[],[f98,f45])).
% 1.57/0.57  fof(f98,plain,(
% 1.57/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_1),
% 1.57/0.57    inference(resolution,[],[f59,f86])).
% 1.57/0.57  fof(f86,plain,(
% 1.57/0.57    ~v1_funct_1(k2_funct_1(sK2)) | spl5_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f84])).
% 1.57/0.57  fof(f59,plain,(
% 1.57/0.57    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f95,plain,(
% 1.57/0.57    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.57/0.57    inference(avatar_split_clause,[],[f50,f92,f88,f84])).
% 1.57/0.57  fof(f50,plain,(
% 1.57/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.57/0.57    inference(cnf_transformation,[],[f34])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (26698)------------------------------
% 1.57/0.57  % (26698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (26698)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (26698)Memory used [KB]: 10874
% 1.57/0.57  % (26698)Time elapsed: 0.125 s
% 1.57/0.57  % (26698)------------------------------
% 1.57/0.57  % (26698)------------------------------
% 1.57/0.57  % (26694)Success in time 0.207 s
%------------------------------------------------------------------------------
