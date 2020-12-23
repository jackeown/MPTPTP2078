%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 207 expanded)
%              Number of leaves         :   33 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  401 ( 681 expanded)
%              Number of equality atoms :   77 ( 114 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f860,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f237,f246,f288,f567,f588,f644,f737,f775,f790,f798,f816,f828,f859])).

fof(f859,plain,
    ( ~ spl5_40
    | ~ spl5_52
    | spl5_54 ),
    inference(avatar_contradiction_clause,[],[f858])).

fof(f858,plain,
    ( $false
    | ~ spl5_40
    | ~ spl5_52
    | spl5_54 ),
    inference(subsumption_resolution,[],[f852,f643])).

fof(f643,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f642])).

fof(f642,plain,
    ( spl5_40
  <=> ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f852,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_52
    | spl5_54 ),
    inference(backward_demodulation,[],[f827,f834])).

fof(f834,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f833,f194])).

fof(f194,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f173,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

% (1056)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f84,f57])).

fof(f57,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f833,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl5_52 ),
    inference(resolution,[],[f815,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f815,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f813])).

fof(f813,plain,
    ( spl5_52
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f827,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl5_54 ),
    inference(avatar_component_clause,[],[f825])).

fof(f825,plain,
    ( spl5_54
  <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f828,plain,
    ( ~ spl5_54
    | spl5_14
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f803,f758,f239,f825])).

fof(f239,plain,
    ( spl5_14
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f758,plain,
    ( spl5_48
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f803,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl5_14
    | ~ spl5_48 ),
    inference(backward_demodulation,[],[f241,f760])).

fof(f760,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f758])).

fof(f241,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f239])).

fof(f816,plain,
    ( spl5_52
    | ~ spl5_48
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f805,f770,f758,f813])).

fof(f770,plain,
    ( spl5_49
  <=> r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f805,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl5_48
    | ~ spl5_49 ),
    inference(forward_demodulation,[],[f801,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f801,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))
    | ~ spl5_48
    | ~ spl5_49 ),
    inference(backward_demodulation,[],[f772,f760])).

fof(f772,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f770])).

fof(f798,plain,
    ( spl5_14
    | ~ spl5_15
    | spl5_48
    | ~ spl5_50 ),
    inference(avatar_contradiction_clause,[],[f797])).

fof(f797,plain,
    ( $false
    | spl5_14
    | ~ spl5_15
    | spl5_48
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f796,f244])).

fof(f244,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl5_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f796,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl5_14
    | spl5_48
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f795,f759])).

fof(f759,plain,
    ( k1_xboole_0 != sK0
    | spl5_48 ),
    inference(avatar_component_clause,[],[f758])).

fof(f795,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl5_14
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f793,f241])).

fof(f793,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl5_50 ),
    inference(trivial_inequality_removal,[],[f792])).

fof(f792,plain,
    ( k1_relat_1(sK1) != k1_relat_1(sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl5_50 ),
    inference(superposition,[],[f88,f783])).

fof(f783,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f781])).

fof(f781,plain,
    ( spl5_50
  <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f790,plain,
    ( spl5_50
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f766,f243,f781])).

fof(f766,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl5_15 ),
    inference(resolution,[],[f244,f85])).

% (1056)Refutation not found, incomplete strategy% (1056)------------------------------
% (1056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1056)Termination reason: Refutation not found, incomplete strategy

% (1056)Memory used [KB]: 6140
% (1056)Time elapsed: 0.086 s
% (1056)------------------------------
% (1056)------------------------------
fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f775,plain,
    ( spl5_49
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f767,f243,f770])).

fof(f767,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))
    | ~ spl5_15 ),
    inference(resolution,[],[f244,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f737,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f735])).

fof(f735,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f107,f122,f93,f245,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

% (1080)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f245,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f243])).

fof(f122,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_4
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f107,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f644,plain,
    ( spl5_40
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f603,f586,f642])).

fof(f586,plain,
    ( spl5_36
  <=> ! [X0] : k1_xboole_0 = sK3(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f603,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0)
    | ~ spl5_36 ),
    inference(superposition,[],[f82,f587])).

fof(f587,plain,
    ( ! [X0] : k1_xboole_0 = sK3(X0,k1_xboole_0)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f586])).

fof(f82,plain,(
    ! [X0,X1] : v1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK3(X0,X1),X0,X1)
      & v1_funct_1(sK3(X0,X1))
      & v5_relat_1(sK3(X0,X1),X1)
      & v4_relat_1(sK3(X0,X1),X0)
      & v1_relat_1(sK3(X0,X1))
      & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK3(X0,X1),X0,X1)
        & v1_funct_1(sK3(X0,X1))
        & v5_relat_1(sK3(X0,X1),X1)
        & v4_relat_1(sK3(X0,X1),X0)
        & v1_relat_1(sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f588,plain,
    ( spl5_36
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f572,f557,f586])).

fof(f557,plain,
    ( spl5_34
  <=> ! [X1,X0] : ~ r2_hidden(X0,sK3(X1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f572,plain,
    ( ! [X0] : k1_xboole_0 = sK3(X0,k1_xboole_0)
    | ~ spl5_34 ),
    inference(resolution,[],[f558,f67])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f558,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,sK3(X1,k1_xboole_0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f557])).

fof(f567,plain,
    ( spl5_34
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f524,f286,f557])).

fof(f286,plain,
    ( spl5_19
  <=> ! [X1] : sP4(sK3(X1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f524,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,sK3(X1,k1_xboole_0))
    | ~ spl5_19 ),
    inference(resolution,[],[f287,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ sP4(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f92,f102_D])).

fof(f102,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP4(X1) ) ),
    inference(cnf_transformation,[],[f102_D])).

fof(f102_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP4(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f287,plain,
    ( ! [X1] : sP4(sK3(X1,k1_xboole_0))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f286])).

fof(f288,plain,
    ( spl5_19
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f253,f235,f286])).

fof(f235,plain,
    ( spl5_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | sP4(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f253,plain,
    ( ! [X1] : sP4(sK3(X1,k1_xboole_0))
    | ~ spl5_13 ),
    inference(resolution,[],[f236,f171])).

fof(f171,plain,(
    ! [X0] : m1_subset_1(sK3(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f77,f95])).

fof(f77,plain,(
    ! [X0,X1] : m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | sP4(X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f235])).

fof(f246,plain,
    ( ~ spl5_14
    | ~ spl5_15
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f233,f110,f243,f239])).

fof(f110,plain,
    ( spl5_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f233,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f55,f112])).

fof(f112,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f55,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f237,plain,
    ( spl5_13
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f176,f115,f235])).

fof(f115,plain,
    ( spl5_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | sP4(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f102,f117])).

fof(f117,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f123,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f54,f120])).

fof(f54,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f118,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f56,f115])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f113,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f53,f110])).

fof(f53,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f108,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f52,f105])).

fof(f52,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:36:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (1048)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.47  % (1069)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (1048)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f860,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f237,f246,f288,f567,f588,f644,f737,f775,f790,f798,f816,f828,f859])).
% 0.20/0.50  fof(f859,plain,(
% 0.20/0.50    ~spl5_40 | ~spl5_52 | spl5_54),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f858])).
% 0.20/0.50  fof(f858,plain,(
% 0.20/0.50    $false | (~spl5_40 | ~spl5_52 | spl5_54)),
% 0.20/0.50    inference(subsumption_resolution,[],[f852,f643])).
% 0.20/0.50  fof(f643,plain,(
% 0.20/0.50    ( ! [X1] : (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)) ) | ~spl5_40),
% 0.20/0.50    inference(avatar_component_clause,[],[f642])).
% 0.20/0.50  fof(f642,plain,(
% 0.20/0.50    spl5_40 <=> ! [X1] : v1_funct_2(k1_xboole_0,X1,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.20/0.50  fof(f852,plain,(
% 0.20/0.50    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl5_52 | spl5_54)),
% 0.20/0.50    inference(backward_demodulation,[],[f827,f834])).
% 0.20/0.50  fof(f834,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~spl5_52),
% 0.20/0.50    inference(subsumption_resolution,[],[f833,f194])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.50    inference(resolution,[],[f173,f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  % (1056)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | r1_tarski(X1,X0)) )),
% 0.20/0.50    inference(superposition,[],[f84,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.50  fof(f833,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | ~spl5_52),
% 0.20/0.50    inference(resolution,[],[f815,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f815,plain,(
% 0.20/0.50    r1_tarski(sK1,k1_xboole_0) | ~spl5_52),
% 0.20/0.50    inference(avatar_component_clause,[],[f813])).
% 0.20/0.50  fof(f813,plain,(
% 0.20/0.50    spl5_52 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.20/0.50  fof(f827,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | spl5_54),
% 0.20/0.50    inference(avatar_component_clause,[],[f825])).
% 0.20/0.50  fof(f825,plain,(
% 0.20/0.50    spl5_54 <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.20/0.50  fof(f828,plain,(
% 0.20/0.50    ~spl5_54 | spl5_14 | ~spl5_48),
% 0.20/0.50    inference(avatar_split_clause,[],[f803,f758,f239,f825])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    spl5_14 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.50  fof(f758,plain,(
% 0.20/0.50    spl5_48 <=> k1_xboole_0 = sK0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 0.20/0.50  fof(f803,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl5_14 | ~spl5_48)),
% 0.20/0.50    inference(backward_demodulation,[],[f241,f760])).
% 0.20/0.50  fof(f760,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | ~spl5_48),
% 0.20/0.50    inference(avatar_component_clause,[],[f758])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl5_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f239])).
% 0.20/0.50  fof(f816,plain,(
% 0.20/0.50    spl5_52 | ~spl5_48 | ~spl5_49),
% 0.20/0.50    inference(avatar_split_clause,[],[f805,f770,f758,f813])).
% 0.20/0.50  fof(f770,plain,(
% 0.20/0.50    spl5_49 <=> r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 0.20/0.50  fof(f805,plain,(
% 0.20/0.50    r1_tarski(sK1,k1_xboole_0) | (~spl5_48 | ~spl5_49)),
% 0.20/0.50    inference(forward_demodulation,[],[f801,f95])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(flattening,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.50  fof(f801,plain,(
% 0.20/0.50    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) | (~spl5_48 | ~spl5_49)),
% 0.20/0.50    inference(backward_demodulation,[],[f772,f760])).
% 0.20/0.50  fof(f772,plain,(
% 0.20/0.50    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) | ~spl5_49),
% 0.20/0.50    inference(avatar_component_clause,[],[f770])).
% 0.20/0.50  fof(f798,plain,(
% 0.20/0.50    spl5_14 | ~spl5_15 | spl5_48 | ~spl5_50),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f797])).
% 0.20/0.50  fof(f797,plain,(
% 0.20/0.50    $false | (spl5_14 | ~spl5_15 | spl5_48 | ~spl5_50)),
% 0.20/0.50    inference(subsumption_resolution,[],[f796,f244])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl5_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f243])).
% 0.20/0.50  fof(f243,plain,(
% 0.20/0.50    spl5_15 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.50  fof(f796,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | (spl5_14 | spl5_48 | ~spl5_50)),
% 0.20/0.50    inference(subsumption_resolution,[],[f795,f759])).
% 0.20/0.50  fof(f759,plain,(
% 0.20/0.50    k1_xboole_0 != sK0 | spl5_48),
% 0.20/0.50    inference(avatar_component_clause,[],[f758])).
% 0.20/0.50  fof(f795,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | (spl5_14 | ~spl5_50)),
% 0.20/0.50    inference(subsumption_resolution,[],[f793,f241])).
% 0.20/0.50  fof(f793,plain,(
% 0.20/0.50    v1_funct_2(sK1,k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl5_50),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f792])).
% 0.20/0.50  fof(f792,plain,(
% 0.20/0.50    k1_relat_1(sK1) != k1_relat_1(sK1) | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl5_50),
% 0.20/0.50    inference(superposition,[],[f88,f783])).
% 0.20/0.50  fof(f783,plain,(
% 0.20/0.50    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl5_50),
% 0.20/0.50    inference(avatar_component_clause,[],[f781])).
% 0.20/0.50  fof(f781,plain,(
% 0.20/0.50    spl5_50 <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f790,plain,(
% 0.20/0.50    spl5_50 | ~spl5_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f766,f243,f781])).
% 0.20/0.50  fof(f766,plain,(
% 0.20/0.50    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl5_15),
% 0.20/0.50    inference(resolution,[],[f244,f85])).
% 0.20/0.50  % (1056)Refutation not found, incomplete strategy% (1056)------------------------------
% 0.20/0.50  % (1056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1056)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1056)Memory used [KB]: 6140
% 0.20/0.50  % (1056)Time elapsed: 0.086 s
% 0.20/0.50  % (1056)------------------------------
% 0.20/0.50  % (1056)------------------------------
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.50  fof(f775,plain,(
% 0.20/0.50    spl5_49 | ~spl5_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f767,f243,f770])).
% 0.20/0.50  fof(f767,plain,(
% 0.20/0.50    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) | ~spl5_15),
% 0.20/0.50    inference(resolution,[],[f244,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f737,plain,(
% 0.20/0.50    ~spl5_1 | ~spl5_4 | spl5_15),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f735])).
% 0.20/0.50  fof(f735,plain,(
% 0.20/0.50    $false | (~spl5_1 | ~spl5_4 | spl5_15)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f107,f122,f93,f245,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  % (1080)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl5_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f243])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    r1_tarski(k2_relat_1(sK1),sK0) | ~spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f120])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    spl5_4 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    v1_relat_1(sK1) | ~spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    spl5_1 <=> v1_relat_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f644,plain,(
% 0.20/0.51    spl5_40 | ~spl5_36),
% 0.20/0.51    inference(avatar_split_clause,[],[f603,f586,f642])).
% 0.20/0.51  fof(f586,plain,(
% 0.20/0.51    spl5_36 <=> ! [X0] : k1_xboole_0 = sK3(X0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.20/0.51  fof(f603,plain,(
% 0.20/0.51    ( ! [X1] : (v1_funct_2(k1_xboole_0,X1,k1_xboole_0)) ) | ~spl5_36),
% 0.20/0.51    inference(superposition,[],[f82,f587])).
% 0.20/0.51  fof(f587,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = sK3(X0,k1_xboole_0)) ) | ~spl5_36),
% 0.20/0.51    inference(avatar_component_clause,[],[f586])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v5_relat_1(sK3(X0,X1),X1) & v4_relat_1(sK3(X0,X1),X0) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v5_relat_1(sK3(X0,X1),X1) & v4_relat_1(sK3(X0,X1),X0) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f20,axiom,(
% 0.20/0.51    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 0.20/0.51  fof(f588,plain,(
% 0.20/0.51    spl5_36 | ~spl5_34),
% 0.20/0.51    inference(avatar_split_clause,[],[f572,f557,f586])).
% 0.20/0.51  fof(f557,plain,(
% 0.20/0.51    spl5_34 <=> ! [X1,X0] : ~r2_hidden(X0,sK3(X1,k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.20/0.51  fof(f572,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = sK3(X0,k1_xboole_0)) ) | ~spl5_34),
% 0.20/0.51    inference(resolution,[],[f558,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.51  fof(f558,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK3(X1,k1_xboole_0))) ) | ~spl5_34),
% 0.20/0.51    inference(avatar_component_clause,[],[f557])).
% 0.20/0.51  fof(f567,plain,(
% 0.20/0.51    spl5_34 | ~spl5_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f524,f286,f557])).
% 0.20/0.51  fof(f286,plain,(
% 0.20/0.51    spl5_19 <=> ! [X1] : sP4(sK3(X1,k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.51  fof(f524,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK3(X1,k1_xboole_0))) ) | ~spl5_19),
% 0.20/0.51    inference(resolution,[],[f287,f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~sP4(X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(general_splitting,[],[f92,f102_D])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP4(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f102_D])).
% 0.20/0.51  fof(f102_D,plain,(
% 0.20/0.51    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP4(X1)) )),
% 0.20/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.51  fof(f287,plain,(
% 0.20/0.51    ( ! [X1] : (sP4(sK3(X1,k1_xboole_0))) ) | ~spl5_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f286])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    spl5_19 | ~spl5_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f253,f235,f286])).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    spl5_13 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | sP4(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    ( ! [X1] : (sP4(sK3(X1,k1_xboole_0))) ) | ~spl5_13),
% 0.20/0.51    inference(resolution,[],[f236,f171])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(sK3(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.51    inference(superposition,[],[f77,f95])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f50])).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | sP4(X0)) ) | ~spl5_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f235])).
% 0.20/0.51  fof(f246,plain,(
% 0.20/0.51    ~spl5_14 | ~spl5_15 | ~spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f233,f110,f243,f239])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl5_2 <=> v1_funct_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f233,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl5_2),
% 0.20/0.51    inference(subsumption_resolution,[],[f55,f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    v1_funct_1(sK1) | ~spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f110])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f21])).
% 0.20/0.51  fof(f21,conjecture,(
% 0.20/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    spl5_13 | ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f176,f115,f235])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    spl5_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | sP4(X0)) ) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f102,f117])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0) | ~spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f115])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f54,f120])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f56,f115])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    spl5_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f53,f110])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    v1_funct_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f52,f105])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (1048)------------------------------
% 0.20/0.51  % (1048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1048)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (1048)Memory used [KB]: 6524
% 0.20/0.51  % (1048)Time elapsed: 0.074 s
% 0.20/0.51  % (1048)------------------------------
% 0.20/0.51  % (1048)------------------------------
% 0.20/0.51  % (1045)Success in time 0.148 s
%------------------------------------------------------------------------------
