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
% DateTime   : Thu Dec  3 13:13:16 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 195 expanded)
%              Number of leaves         :   35 (  88 expanded)
%              Depth                    :    7
%              Number of atoms          :  336 ( 530 expanded)
%              Number of equality atoms :   35 (  61 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f70,f78,f82,f86,f90,f94,f98,f102,f110,f125,f129,f159,f175,f185,f198,f202,f213,f231,f246,f259,f276,f294])).

fof(f294,plain,
    ( ~ spl4_6
    | ~ spl4_11
    | spl4_38
    | ~ spl4_43 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_11
    | spl4_38
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f288,f77])).

fof(f77,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f288,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_11
    | spl4_38
    | ~ spl4_43 ),
    inference(backward_demodulation,[],[f245,f280])).

fof(f280,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_43 ),
    inference(resolution,[],[f275,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_11
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK2(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f275,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_tarski(k1_xboole_0))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl4_43
  <=> ! [X1] : ~ r2_hidden(X1,k3_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f245,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl4_38
  <=> v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f276,plain,
    ( spl4_43
    | ~ spl4_9
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f265,f257,f88,f274])).

fof(f88,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f257,plain,
    ( spl4_40
  <=> ! [X0] : r1_tarski(k3_tarski(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f265,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_tarski(k1_xboole_0))
    | ~ spl4_9
    | ~ spl4_40 ),
    inference(resolution,[],[f258,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,X0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f258,plain,
    ( ! [X0] : r1_tarski(k3_tarski(k1_xboole_0),X0)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f257])).

fof(f259,plain,
    ( spl4_40
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f203,f196,f100,f257])).

fof(f100,plain,
    ( spl4_12
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f196,plain,
    ( spl4_30
  <=> ! [X4] : r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f203,plain,
    ( ! [X0] : r1_tarski(k3_tarski(k1_xboole_0),X0)
    | ~ spl4_12
    | ~ spl4_30 ),
    inference(resolution,[],[f197,f101])).

fof(f101,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f197,plain,
    ( ! [X4] : r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(X4))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f196])).

fof(f246,plain,
    ( ~ spl4_38
    | spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f238,f229,f92,f60,f56,f244])).

fof(f56,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f60,plain,
    ( spl4_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f92,plain,
    ( spl4_10
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f229,plain,
    ( spl4_35
  <=> u1_struct_0(sK0) = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f238,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f237,f57])).

fof(f57,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f237,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_10
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f236,f61])).

fof(f61,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f236,plain,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_10
    | ~ spl4_35 ),
    inference(superposition,[],[f93,f230])).

fof(f230,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_xboole_0)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f229])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f92])).

fof(f231,plain,
    ( spl4_35
    | ~ spl4_8
    | ~ spl4_17
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f219,f211,f123,f84,f229])).

fof(f84,plain,
    ( spl4_8
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f123,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f211,plain,
    ( spl4_33
  <=> u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f219,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_xboole_0)
    | ~ spl4_8
    | ~ spl4_17
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f216,f85])).

fof(f85,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f216,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_17
    | ~ spl4_33 ),
    inference(superposition,[],[f212,f124])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( k5_setfam_1(X0,X1) = k3_tarski(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f123])).

fof(f212,plain,
    ( u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
    ( spl4_33
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f204,f200,f68,f211])).

fof(f68,plain,
    ( spl4_4
  <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f200,plain,
    ( spl4_31
  <=> ! [X0] :
        ( k5_setfam_1(X0,k1_xboole_0) = X0
        | ~ m1_setfam_1(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f204,plain,
    ( u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(resolution,[],[f201,f69])).

fof(f69,plain,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_setfam_1(k1_xboole_0,X0)
        | k5_setfam_1(X0,k1_xboole_0) = X0 )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( spl4_31
    | ~ spl4_8
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f186,f157,f84,f200])).

fof(f157,plain,
    ( spl4_24
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k5_setfam_1(X0,X1) = X0
        | ~ m1_setfam_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

% (32076)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f186,plain,
    ( ! [X0] :
        ( k5_setfam_1(X0,k1_xboole_0) = X0
        | ~ m1_setfam_1(k1_xboole_0,X0) )
    | ~ spl4_8
    | ~ spl4_24 ),
    inference(resolution,[],[f158,f85])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k5_setfam_1(X0,X1) = X0
        | ~ m1_setfam_1(X1,X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f157])).

fof(f198,plain,
    ( spl4_30
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f192,f183,f108,f80,f196])).

fof(f80,plain,
    ( spl4_7
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f108,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f183,plain,
    ( spl4_29
  <=> ! [X0] : m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f192,plain,
    ( ! [X4] : r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(X4))
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f191,f81])).

fof(f81,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f191,plain,
    ( ! [X4] :
        ( v1_xboole_0(k1_zfmisc_1(X4))
        | r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(X4)) )
    | ~ spl4_14
    | ~ spl4_29 ),
    inference(resolution,[],[f184,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f184,plain,
    ( ! [X0] : m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f183])).

fof(f185,plain,
    ( spl4_29
    | ~ spl4_8
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f181,f173,f123,f84,f183])).

fof(f173,plain,
    ( spl4_28
  <=> ! [X0] : m1_subset_1(k5_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f181,plain,
    ( ! [X0] : m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl4_8
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f179,f85])).

fof(f179,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(superposition,[],[f174,f124])).

fof(f174,plain,
    ( ! [X0] : m1_subset_1(k5_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f173])).

fof(f175,plain,
    ( spl4_28
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f136,f127,f84,f173])).

fof(f127,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f136,plain,
    ( ! [X0] : m1_subset_1(k5_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(resolution,[],[f128,f85])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f159,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f44,f157])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = X0
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f129,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f42,f127])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f125,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f41,f123])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f110,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f40,f108])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f102,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f51,f100])).

fof(f51,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f98,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f94,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f36,f92])).

% (32076)Refutation not found, incomplete strategy% (32076)------------------------------
% (32076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f36,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

% (32076)Termination reason: Refutation not found, incomplete strategy

% (32076)Memory used [KB]: 6140
% (32076)Time elapsed: 0.099 s
% (32076)------------------------------
% (32076)------------------------------
fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f90,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f49,f88])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f86,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f35,f84])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f82,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f78,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f70,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f53,f68])).

fof(f53,plain,(
    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f29,f30])).

fof(f30,plain,(
    k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = X1
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( k1_xboole_0 = X1
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ~ ( k1_xboole_0 = X1
              & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(f29,plain,(
    m1_setfam_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:59:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (32077)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (32091)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (32091)Refutation not found, incomplete strategy% (32091)------------------------------
% 0.21/0.50  % (32091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32091)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32091)Memory used [KB]: 6140
% 0.21/0.50  % (32091)Time elapsed: 0.009 s
% 0.21/0.50  % (32091)------------------------------
% 0.21/0.50  % (32091)------------------------------
% 0.21/0.50  % (32083)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (32077)Refutation not found, incomplete strategy% (32077)------------------------------
% 0.21/0.50  % (32077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32077)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32077)Memory used [KB]: 10490
% 0.21/0.50  % (32077)Time elapsed: 0.072 s
% 0.21/0.50  % (32077)------------------------------
% 0.21/0.50  % (32077)------------------------------
% 0.21/0.52  % (32084)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (32085)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (32092)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (32090)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.53  % (32081)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.33/0.53  % (32085)Refutation found. Thanks to Tanya!
% 1.33/0.53  % SZS status Theorem for theBenchmark
% 1.33/0.53  % SZS output start Proof for theBenchmark
% 1.33/0.53  fof(f295,plain,(
% 1.33/0.53    $false),
% 1.33/0.53    inference(avatar_sat_refutation,[],[f58,f62,f70,f78,f82,f86,f90,f94,f98,f102,f110,f125,f129,f159,f175,f185,f198,f202,f213,f231,f246,f259,f276,f294])).
% 1.33/0.53  fof(f294,plain,(
% 1.33/0.53    ~spl4_6 | ~spl4_11 | spl4_38 | ~spl4_43),
% 1.33/0.53    inference(avatar_contradiction_clause,[],[f293])).
% 1.33/0.53  fof(f293,plain,(
% 1.33/0.53    $false | (~spl4_6 | ~spl4_11 | spl4_38 | ~spl4_43)),
% 1.33/0.53    inference(subsumption_resolution,[],[f288,f77])).
% 1.33/0.53  fof(f77,plain,(
% 1.33/0.53    v1_xboole_0(k1_xboole_0) | ~spl4_6),
% 1.33/0.53    inference(avatar_component_clause,[],[f76])).
% 1.33/0.53  fof(f76,plain,(
% 1.33/0.53    spl4_6 <=> v1_xboole_0(k1_xboole_0)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.33/0.53  fof(f288,plain,(
% 1.33/0.53    ~v1_xboole_0(k1_xboole_0) | (~spl4_11 | spl4_38 | ~spl4_43)),
% 1.33/0.53    inference(backward_demodulation,[],[f245,f280])).
% 1.33/0.53  fof(f280,plain,(
% 1.33/0.53    k1_xboole_0 = k3_tarski(k1_xboole_0) | (~spl4_11 | ~spl4_43)),
% 1.33/0.53    inference(resolution,[],[f275,f97])).
% 1.33/0.53  fof(f97,plain,(
% 1.33/0.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_11),
% 1.33/0.53    inference(avatar_component_clause,[],[f96])).
% 1.33/0.53  fof(f96,plain,(
% 1.33/0.53    spl4_11 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0))),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.33/0.54  fof(f275,plain,(
% 1.33/0.54    ( ! [X1] : (~r2_hidden(X1,k3_tarski(k1_xboole_0))) ) | ~spl4_43),
% 1.33/0.54    inference(avatar_component_clause,[],[f274])).
% 1.33/0.54  fof(f274,plain,(
% 1.33/0.54    spl4_43 <=> ! [X1] : ~r2_hidden(X1,k3_tarski(k1_xboole_0))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.33/0.54  fof(f245,plain,(
% 1.33/0.54    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | spl4_38),
% 1.33/0.54    inference(avatar_component_clause,[],[f244])).
% 1.33/0.54  fof(f244,plain,(
% 1.33/0.54    spl4_38 <=> v1_xboole_0(k3_tarski(k1_xboole_0))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.33/0.54  fof(f276,plain,(
% 1.33/0.54    spl4_43 | ~spl4_9 | ~spl4_40),
% 1.33/0.54    inference(avatar_split_clause,[],[f265,f257,f88,f274])).
% 1.33/0.54  fof(f88,plain,(
% 1.33/0.54    spl4_9 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.33/0.54  fof(f257,plain,(
% 1.33/0.54    spl4_40 <=> ! [X0] : r1_tarski(k3_tarski(k1_xboole_0),X0)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.33/0.54  fof(f265,plain,(
% 1.33/0.54    ( ! [X1] : (~r2_hidden(X1,k3_tarski(k1_xboole_0))) ) | (~spl4_9 | ~spl4_40)),
% 1.33/0.54    inference(resolution,[],[f258,f89])).
% 1.33/0.54  fof(f89,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) ) | ~spl4_9),
% 1.33/0.54    inference(avatar_component_clause,[],[f88])).
% 1.33/0.54  fof(f258,plain,(
% 1.33/0.54    ( ! [X0] : (r1_tarski(k3_tarski(k1_xboole_0),X0)) ) | ~spl4_40),
% 1.33/0.54    inference(avatar_component_clause,[],[f257])).
% 1.33/0.54  fof(f259,plain,(
% 1.33/0.54    spl4_40 | ~spl4_12 | ~spl4_30),
% 1.33/0.54    inference(avatar_split_clause,[],[f203,f196,f100,f257])).
% 1.33/0.54  fof(f100,plain,(
% 1.33/0.54    spl4_12 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0)))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.33/0.54  fof(f196,plain,(
% 1.33/0.54    spl4_30 <=> ! [X4] : r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(X4))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.33/0.54  fof(f203,plain,(
% 1.33/0.54    ( ! [X0] : (r1_tarski(k3_tarski(k1_xboole_0),X0)) ) | (~spl4_12 | ~spl4_30)),
% 1.33/0.54    inference(resolution,[],[f197,f101])).
% 1.33/0.54  fof(f101,plain,(
% 1.33/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) ) | ~spl4_12),
% 1.33/0.54    inference(avatar_component_clause,[],[f100])).
% 1.33/0.54  fof(f197,plain,(
% 1.33/0.54    ( ! [X4] : (r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(X4))) ) | ~spl4_30),
% 1.33/0.54    inference(avatar_component_clause,[],[f196])).
% 1.33/0.54  fof(f246,plain,(
% 1.33/0.54    ~spl4_38 | spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_35),
% 1.33/0.54    inference(avatar_split_clause,[],[f238,f229,f92,f60,f56,f244])).
% 1.33/0.54  fof(f56,plain,(
% 1.33/0.54    spl4_1 <=> v2_struct_0(sK0)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.33/0.54  fof(f60,plain,(
% 1.33/0.54    spl4_2 <=> l1_struct_0(sK0)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.33/0.54  fof(f92,plain,(
% 1.33/0.54    spl4_10 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.33/0.54  fof(f229,plain,(
% 1.33/0.54    spl4_35 <=> u1_struct_0(sK0) = k3_tarski(k1_xboole_0)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.33/0.54  fof(f238,plain,(
% 1.33/0.54    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | (spl4_1 | ~spl4_2 | ~spl4_10 | ~spl4_35)),
% 1.33/0.54    inference(subsumption_resolution,[],[f237,f57])).
% 1.33/0.54  fof(f57,plain,(
% 1.33/0.54    ~v2_struct_0(sK0) | spl4_1),
% 1.33/0.54    inference(avatar_component_clause,[],[f56])).
% 1.33/0.54  fof(f237,plain,(
% 1.33/0.54    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_10 | ~spl4_35)),
% 1.33/0.54    inference(subsumption_resolution,[],[f236,f61])).
% 1.33/0.54  fof(f61,plain,(
% 1.33/0.54    l1_struct_0(sK0) | ~spl4_2),
% 1.33/0.54    inference(avatar_component_clause,[],[f60])).
% 1.33/0.54  fof(f236,plain,(
% 1.33/0.54    ~v1_xboole_0(k3_tarski(k1_xboole_0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl4_10 | ~spl4_35)),
% 1.33/0.54    inference(superposition,[],[f93,f230])).
% 1.33/0.54  fof(f230,plain,(
% 1.33/0.54    u1_struct_0(sK0) = k3_tarski(k1_xboole_0) | ~spl4_35),
% 1.33/0.54    inference(avatar_component_clause,[],[f229])).
% 1.33/0.54  fof(f93,plain,(
% 1.33/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl4_10),
% 1.33/0.54    inference(avatar_component_clause,[],[f92])).
% 1.33/0.54  fof(f231,plain,(
% 1.33/0.54    spl4_35 | ~spl4_8 | ~spl4_17 | ~spl4_33),
% 1.33/0.54    inference(avatar_split_clause,[],[f219,f211,f123,f84,f229])).
% 1.33/0.54  fof(f84,plain,(
% 1.33/0.54    spl4_8 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.33/0.54  fof(f123,plain,(
% 1.33/0.54    spl4_17 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k5_setfam_1(X0,X1) = k3_tarski(X1))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.33/0.54  fof(f211,plain,(
% 1.33/0.54    spl4_33 <=> u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.33/0.54  fof(f219,plain,(
% 1.33/0.54    u1_struct_0(sK0) = k3_tarski(k1_xboole_0) | (~spl4_8 | ~spl4_17 | ~spl4_33)),
% 1.33/0.54    inference(subsumption_resolution,[],[f216,f85])).
% 1.33/0.54  fof(f85,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl4_8),
% 1.33/0.54    inference(avatar_component_clause,[],[f84])).
% 1.33/0.54  fof(f216,plain,(
% 1.33/0.54    u1_struct_0(sK0) = k3_tarski(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl4_17 | ~spl4_33)),
% 1.33/0.54    inference(superposition,[],[f212,f124])).
% 1.33/0.54  fof(f124,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k5_setfam_1(X0,X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl4_17),
% 1.33/0.54    inference(avatar_component_clause,[],[f123])).
% 1.33/0.54  fof(f212,plain,(
% 1.33/0.54    u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) | ~spl4_33),
% 1.33/0.54    inference(avatar_component_clause,[],[f211])).
% 1.33/0.54  fof(f213,plain,(
% 1.33/0.54    spl4_33 | ~spl4_4 | ~spl4_31),
% 1.33/0.54    inference(avatar_split_clause,[],[f204,f200,f68,f211])).
% 1.33/0.54  fof(f68,plain,(
% 1.33/0.54    spl4_4 <=> m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.33/0.54  fof(f200,plain,(
% 1.33/0.54    spl4_31 <=> ! [X0] : (k5_setfam_1(X0,k1_xboole_0) = X0 | ~m1_setfam_1(k1_xboole_0,X0))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.33/0.54  fof(f204,plain,(
% 1.33/0.54    u1_struct_0(sK0) = k5_setfam_1(u1_struct_0(sK0),k1_xboole_0) | (~spl4_4 | ~spl4_31)),
% 1.33/0.54    inference(resolution,[],[f201,f69])).
% 1.33/0.54  fof(f69,plain,(
% 1.33/0.54    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) | ~spl4_4),
% 1.33/0.54    inference(avatar_component_clause,[],[f68])).
% 1.33/0.54  fof(f201,plain,(
% 1.33/0.54    ( ! [X0] : (~m1_setfam_1(k1_xboole_0,X0) | k5_setfam_1(X0,k1_xboole_0) = X0) ) | ~spl4_31),
% 1.33/0.54    inference(avatar_component_clause,[],[f200])).
% 1.33/0.54  fof(f202,plain,(
% 1.33/0.54    spl4_31 | ~spl4_8 | ~spl4_24),
% 1.33/0.54    inference(avatar_split_clause,[],[f186,f157,f84,f200])).
% 1.33/0.54  fof(f157,plain,(
% 1.33/0.54    spl4_24 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.33/0.54  % (32076)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.33/0.54  fof(f186,plain,(
% 1.33/0.54    ( ! [X0] : (k5_setfam_1(X0,k1_xboole_0) = X0 | ~m1_setfam_1(k1_xboole_0,X0)) ) | (~spl4_8 | ~spl4_24)),
% 1.33/0.54    inference(resolution,[],[f158,f85])).
% 1.33/0.54  fof(f158,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0)) ) | ~spl4_24),
% 1.33/0.54    inference(avatar_component_clause,[],[f157])).
% 1.33/0.54  fof(f198,plain,(
% 1.33/0.54    spl4_30 | ~spl4_7 | ~spl4_14 | ~spl4_29),
% 1.33/0.54    inference(avatar_split_clause,[],[f192,f183,f108,f80,f196])).
% 1.33/0.54  fof(f80,plain,(
% 1.33/0.54    spl4_7 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.33/0.54  fof(f108,plain,(
% 1.33/0.54    spl4_14 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.33/0.54  fof(f183,plain,(
% 1.33/0.54    spl4_29 <=> ! [X0] : m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.33/0.54  fof(f192,plain,(
% 1.33/0.54    ( ! [X4] : (r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(X4))) ) | (~spl4_7 | ~spl4_14 | ~spl4_29)),
% 1.33/0.54    inference(subsumption_resolution,[],[f191,f81])).
% 1.33/0.54  fof(f81,plain,(
% 1.33/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl4_7),
% 1.33/0.54    inference(avatar_component_clause,[],[f80])).
% 1.33/0.54  fof(f191,plain,(
% 1.33/0.54    ( ! [X4] : (v1_xboole_0(k1_zfmisc_1(X4)) | r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(X4))) ) | (~spl4_14 | ~spl4_29)),
% 1.33/0.54    inference(resolution,[],[f184,f109])).
% 1.33/0.54  fof(f109,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) ) | ~spl4_14),
% 1.33/0.54    inference(avatar_component_clause,[],[f108])).
% 1.33/0.54  fof(f184,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0))) ) | ~spl4_29),
% 1.33/0.54    inference(avatar_component_clause,[],[f183])).
% 1.33/0.54  fof(f185,plain,(
% 1.33/0.54    spl4_29 | ~spl4_8 | ~spl4_17 | ~spl4_28),
% 1.33/0.54    inference(avatar_split_clause,[],[f181,f173,f123,f84,f183])).
% 1.33/0.54  fof(f173,plain,(
% 1.33/0.54    spl4_28 <=> ! [X0] : m1_subset_1(k5_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.33/0.54  fof(f181,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0))) ) | (~spl4_8 | ~spl4_17 | ~spl4_28)),
% 1.33/0.54    inference(subsumption_resolution,[],[f179,f85])).
% 1.33/0.54  fof(f179,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl4_17 | ~spl4_28)),
% 1.33/0.54    inference(superposition,[],[f174,f124])).
% 1.33/0.54  fof(f174,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(k5_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) ) | ~spl4_28),
% 1.33/0.54    inference(avatar_component_clause,[],[f173])).
% 1.33/0.54  fof(f175,plain,(
% 1.33/0.54    spl4_28 | ~spl4_8 | ~spl4_18),
% 1.33/0.54    inference(avatar_split_clause,[],[f136,f127,f84,f173])).
% 1.33/0.54  fof(f127,plain,(
% 1.33/0.54    spl4_18 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.33/0.54  fof(f136,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(k5_setfam_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) ) | (~spl4_8 | ~spl4_18)),
% 1.33/0.54    inference(resolution,[],[f128,f85])).
% 1.33/0.54  fof(f128,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))) ) | ~spl4_18),
% 1.33/0.54    inference(avatar_component_clause,[],[f127])).
% 1.33/0.54  fof(f159,plain,(
% 1.33/0.54    spl4_24),
% 1.33/0.54    inference(avatar_split_clause,[],[f44,f157])).
% 1.33/0.54  fof(f44,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f24])).
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ! [X0,X1] : ((m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.54    inference(ennf_transformation,[],[f9])).
% 1.33/0.54  fof(f9,axiom,(
% 1.33/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).
% 1.33/0.54  fof(f129,plain,(
% 1.33/0.54    spl4_18),
% 1.33/0.54    inference(avatar_split_clause,[],[f42,f127])).
% 1.33/0.54  fof(f42,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f23])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.54    inference(ennf_transformation,[],[f5])).
% 1.33/0.54  fof(f5,axiom,(
% 1.33/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 1.33/0.54  fof(f125,plain,(
% 1.33/0.54    spl4_17),
% 1.33/0.54    inference(avatar_split_clause,[],[f41,f123])).
% 1.33/0.54  fof(f41,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k5_setfam_1(X0,X1) = k3_tarski(X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    ! [X0,X1] : (k5_setfam_1(X0,X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k5_setfam_1(X0,X1) = k3_tarski(X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 1.33/0.54  fof(f110,plain,(
% 1.33/0.54    spl4_14),
% 1.33/0.54    inference(avatar_split_clause,[],[f40,f108])).
% 1.33/0.54  fof(f40,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f21])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.33/0.54    inference(flattening,[],[f20])).
% 1.33/0.54  fof(f20,plain,(
% 1.33/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.33/0.54    inference(ennf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,axiom,(
% 1.33/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.33/0.54  fof(f102,plain,(
% 1.33/0.54    spl4_12),
% 1.33/0.54    inference(avatar_split_clause,[],[f51,f100])).
% 1.33/0.54  fof(f51,plain,(
% 1.33/0.54    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.33/0.54    inference(equality_resolution,[],[f46])).
% 1.33/0.54  fof(f46,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f2])).
% 1.33/0.54  fof(f2,axiom,(
% 1.33/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.33/0.54  fof(f98,plain,(
% 1.33/0.54    spl4_11),
% 1.33/0.54    inference(avatar_split_clause,[],[f39,f96])).
% 1.33/0.54  fof(f39,plain,(
% 1.33/0.54    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f19])).
% 1.33/0.54  fof(f19,plain,(
% 1.33/0.54    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.33/0.54    inference(ennf_transformation,[],[f11])).
% 1.33/0.54  fof(f11,axiom,(
% 1.33/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.33/0.54  fof(f94,plain,(
% 1.33/0.54    spl4_10),
% 1.33/0.54    inference(avatar_split_clause,[],[f36,f92])).
% 1.33/0.54  % (32076)Refutation not found, incomplete strategy% (32076)------------------------------
% 1.33/0.54  % (32076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  fof(f36,plain,(
% 1.33/0.54    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f18])).
% 1.33/0.54  % (32076)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (32076)Memory used [KB]: 6140
% 1.33/0.54  % (32076)Time elapsed: 0.099 s
% 1.33/0.54  % (32076)------------------------------
% 1.33/0.54  % (32076)------------------------------
% 1.33/0.54  fof(f18,plain,(
% 1.33/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f17])).
% 1.33/0.54  fof(f17,plain,(
% 1.33/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f12])).
% 1.33/0.54  fof(f12,axiom,(
% 1.33/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.33/0.54  fof(f90,plain,(
% 1.33/0.54    spl4_9),
% 1.33/0.54    inference(avatar_split_clause,[],[f49,f88])).
% 1.33/0.54  fof(f49,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f25])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.33/0.54    inference(ennf_transformation,[],[f10])).
% 1.33/0.54  fof(f10,axiom,(
% 1.33/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.33/0.54  fof(f86,plain,(
% 1.33/0.54    spl4_8),
% 1.33/0.54    inference(avatar_split_clause,[],[f35,f84])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f4])).
% 1.33/0.54  fof(f4,axiom,(
% 1.33/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.33/0.54  fof(f82,plain,(
% 1.33/0.54    spl4_7),
% 1.33/0.54    inference(avatar_split_clause,[],[f34,f80])).
% 1.33/0.54  fof(f34,plain,(
% 1.33/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.33/0.54  fof(f78,plain,(
% 1.33/0.54    spl4_6),
% 1.33/0.54    inference(avatar_split_clause,[],[f33,f76])).
% 1.33/0.54  fof(f33,plain,(
% 1.33/0.54    v1_xboole_0(k1_xboole_0)),
% 1.33/0.54    inference(cnf_transformation,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    v1_xboole_0(k1_xboole_0)),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.33/0.54  fof(f70,plain,(
% 1.33/0.54    spl4_4),
% 1.33/0.54    inference(avatar_split_clause,[],[f53,f68])).
% 1.33/0.54  fof(f53,plain,(
% 1.33/0.54    m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))),
% 1.33/0.54    inference(forward_demodulation,[],[f29,f30])).
% 1.33/0.54  fof(f30,plain,(
% 1.33/0.54    k1_xboole_0 = sK1),
% 1.33/0.54    inference(cnf_transformation,[],[f16])).
% 1.33/0.54  fof(f16,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.33/0.54    inference(flattening,[],[f15])).
% 1.33/0.54  fof(f15,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : ((k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f14])).
% 1.33/0.54  fof(f14,negated_conjecture,(
% 1.33/0.54    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 1.33/0.54    inference(negated_conjecture,[],[f13])).
% 1.33/0.54  fof(f13,conjecture,(
% 1.33/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X1 & m1_setfam_1(X1,u1_struct_0(X0)))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).
% 1.33/0.54  fof(f29,plain,(
% 1.33/0.54    m1_setfam_1(sK1,u1_struct_0(sK0))),
% 1.33/0.54    inference(cnf_transformation,[],[f16])).
% 1.33/0.54  fof(f62,plain,(
% 1.33/0.54    spl4_2),
% 1.33/0.54    inference(avatar_split_clause,[],[f32,f60])).
% 1.33/0.54  fof(f32,plain,(
% 1.33/0.54    l1_struct_0(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f16])).
% 1.33/0.54  fof(f58,plain,(
% 1.33/0.54    ~spl4_1),
% 1.33/0.54    inference(avatar_split_clause,[],[f31,f56])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    ~v2_struct_0(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f16])).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (32085)------------------------------
% 1.33/0.54  % (32085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (32085)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (32085)Memory used [KB]: 10746
% 1.33/0.54  % (32085)Time elapsed: 0.098 s
% 1.33/0.54  % (32085)------------------------------
% 1.33/0.54  % (32085)------------------------------
% 1.33/0.54  % (32075)Success in time 0.176 s
%------------------------------------------------------------------------------
