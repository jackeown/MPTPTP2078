%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:37 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 252 expanded)
%              Number of leaves         :   36 ( 108 expanded)
%              Depth                    :    9
%              Number of atoms          :  331 ( 573 expanded)
%              Number of equality atoms :   75 ( 154 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f354,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f107,f112,f138,f143,f150,f168,f194,f208,f231,f240,f246,f249,f297,f336,f339,f349,f353])).

fof(f353,plain,(
    spl4_35 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | spl4_35 ),
    inference(unit_resulting_resolution,[],[f39,f348,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

% (31264)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (31263)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% (31269)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (31279)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (31267)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f348,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl4_35
  <=> r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f349,plain,
    ( ~ spl4_35
    | spl4_19
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f342,f329,f191,f346])).

fof(f191,plain,
    ( spl4_19
  <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f329,plain,
    ( spl4_33
  <=> k1_xboole_0 = k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f342,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl4_19
    | ~ spl4_33 ),
    inference(backward_demodulation,[],[f193,f331])).

fof(f331,plain,
    ( k1_xboole_0 = k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f329])).

fof(f193,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f339,plain,(
    spl4_34 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl4_34 ),
    inference(unit_resulting_resolution,[],[f39,f335,f52])).

fof(f335,plain,
    ( ~ r1_tarski(k1_xboole_0,k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl4_34
  <=> r1_tarski(k1_xboole_0,k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f336,plain,
    ( spl4_33
    | ~ spl4_34
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f298,f294,f333,f329])).

fof(f294,plain,
    ( spl4_30
  <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f298,plain,
    ( ~ r1_tarski(k1_xboole_0,k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2))
    | k1_xboole_0 = k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2)
    | ~ spl4_30 ),
    inference(resolution,[],[f296,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f296,plain,
    ( r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k1_xboole_0)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f294])).

fof(f297,plain,
    ( spl4_30
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f266,f237,f223,f294])).

fof(f223,plain,
    ( spl4_22
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f237,plain,
    ( spl4_24
  <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f266,plain,
    ( r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k1_xboole_0)
    | ~ spl4_22
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f238,f225])).

fof(f225,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f223])).

fof(f238,plain,
    ( r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f237])).

fof(f249,plain,
    ( ~ spl4_5
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl4_5
    | spl4_25 ),
    inference(unit_resulting_resolution,[],[f106,f245,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f245,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl4_25
  <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f106,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f246,plain,
    ( ~ spl4_15
    | ~ spl4_25
    | spl4_24 ),
    inference(avatar_split_clause,[],[f241,f237,f243,f165])).

fof(f165,plain,
    ( spl4_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f241,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | spl4_24 ),
    inference(superposition,[],[f239,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f239,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f237])).

fof(f240,plain,
    ( ~ spl4_24
    | spl4_11
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f234,f205,f147,f135,f237])).

fof(f135,plain,
    ( spl4_11
  <=> r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f147,plain,
    ( spl4_13
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f205,plain,
    ( spl4_20
  <=> k2_relat_1(sK3) = k11_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f234,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))
    | spl4_11
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f233,f149])).

fof(f149,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f233,plain,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_relat_1(sK3))
    | spl4_11
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f137,f207])).

fof(f207,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f205])).

fof(f137,plain,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f231,plain,
    ( spl4_10
    | ~ spl4_5
    | spl4_22
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f209,f205,f223,f104,f131])).

fof(f131,plain,
    ( spl4_10
  <=> r2_hidden(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f209,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | r2_hidden(sK0,k1_relat_1(sK3))
    | ~ spl4_20 ),
    inference(superposition,[],[f207,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f208,plain,
    ( ~ spl4_5
    | spl4_20
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f199,f147,f205,f104])).

fof(f199,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( k2_relat_1(sK3) = k11_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(superposition,[],[f41,f158])).

fof(f158,plain,
    ( ! [X0] :
        ( k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK3))
        | ~ v1_relat_1(X0) )
    | ~ spl4_13 ),
    inference(superposition,[],[f69,f149])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f41,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f194,plain,
    ( ~ spl4_19
    | spl4_6
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f154,f147,f109,f191])).

fof(f109,plain,
    ( spl4_6
  <=> r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f154,plain,
    ( ~ r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl4_6
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f111,f149])).

fof(f111,plain,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f168,plain,
    ( spl4_15
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f152,f147,f94,f165])).

fof(f94,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f152,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f96,f149])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f150,plain,
    ( ~ spl4_4
    | spl4_13
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f144,f140,f147,f94])).

fof(f140,plain,
    ( spl4_12
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f144,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl4_12 ),
    inference(superposition,[],[f142,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f142,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f143,plain,
    ( ~ spl4_3
    | spl4_12
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f99,f94,f84,f140,f89])).

fof(f89,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f84,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3)
    | ~ v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f96,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f138,plain,
    ( ~ spl4_5
    | ~ spl4_10
    | ~ spl4_1
    | ~ spl4_11
    | spl4_6 ),
    inference(avatar_split_clause,[],[f129,f109,f135,f79,f131,f104])).

fof(f79,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f129,plain,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0))
    | ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_6 ),
    inference(superposition,[],[f111,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f112,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f66,f109])).

fof(f66,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f38,f65,f65])).

fof(f38,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(f107,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f100,f94,f104])).

fof(f100,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f96,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f97,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f67,f94])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f36,f65])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f92,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f68,f89])).

fof(f68,plain,(
    v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f35,f65])).

fof(f35,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (31275)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (31270)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.54  % (31283)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.54  % (31291)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.55  % (31285)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.55  % (31271)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.55  % (31291)Refutation found. Thanks to Tanya!
% 1.38/0.55  % SZS status Theorem for theBenchmark
% 1.38/0.55  % SZS output start Proof for theBenchmark
% 1.38/0.55  fof(f354,plain,(
% 1.38/0.55    $false),
% 1.38/0.55    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f107,f112,f138,f143,f150,f168,f194,f208,f231,f240,f246,f249,f297,f336,f339,f349,f353])).
% 1.38/0.55  fof(f353,plain,(
% 1.38/0.55    spl4_35),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f351])).
% 1.38/0.55  fof(f351,plain,(
% 1.38/0.55    $false | spl4_35),
% 1.38/0.55    inference(unit_resulting_resolution,[],[f39,f348,f52])).
% 1.38/0.55  fof(f52,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f6])).
% 1.38/0.55  % (31264)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.38/0.55  % (31263)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.55/0.56  % (31269)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.57  % (31279)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.55/0.57  % (31267)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.55/0.57  fof(f6,axiom,(
% 1.55/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.55/0.57  fof(f348,plain,(
% 1.55/0.57    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl4_35),
% 1.55/0.57    inference(avatar_component_clause,[],[f346])).
% 1.55/0.57  fof(f346,plain,(
% 1.55/0.57    spl4_35 <=> r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.55/0.57  fof(f39,plain,(
% 1.55/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f5])).
% 1.55/0.57  fof(f5,axiom,(
% 1.55/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.55/0.57  fof(f349,plain,(
% 1.55/0.57    ~spl4_35 | spl4_19 | ~spl4_33),
% 1.55/0.57    inference(avatar_split_clause,[],[f342,f329,f191,f346])).
% 1.55/0.57  fof(f191,plain,(
% 1.55/0.57    spl4_19 <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.55/0.57  fof(f329,plain,(
% 1.55/0.57    spl4_33 <=> k1_xboole_0 = k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.55/0.57  fof(f342,plain,(
% 1.55/0.57    ~r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | (spl4_19 | ~spl4_33)),
% 1.55/0.57    inference(backward_demodulation,[],[f193,f331])).
% 1.55/0.57  fof(f331,plain,(
% 1.55/0.57    k1_xboole_0 = k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2) | ~spl4_33),
% 1.55/0.57    inference(avatar_component_clause,[],[f329])).
% 1.55/0.57  fof(f193,plain,(
% 1.55/0.57    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl4_19),
% 1.55/0.57    inference(avatar_component_clause,[],[f191])).
% 1.55/0.57  fof(f339,plain,(
% 1.55/0.57    spl4_34),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f337])).
% 1.55/0.57  fof(f337,plain,(
% 1.55/0.57    $false | spl4_34),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f39,f335,f52])).
% 1.55/0.57  fof(f335,plain,(
% 1.55/0.57    ~r1_tarski(k1_xboole_0,k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2)) | spl4_34),
% 1.55/0.57    inference(avatar_component_clause,[],[f333])).
% 1.55/0.57  fof(f333,plain,(
% 1.55/0.57    spl4_34 <=> r1_tarski(k1_xboole_0,k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.55/0.57  fof(f336,plain,(
% 1.55/0.57    spl4_33 | ~spl4_34 | ~spl4_30),
% 1.55/0.57    inference(avatar_split_clause,[],[f298,f294,f333,f329])).
% 1.55/0.57  fof(f294,plain,(
% 1.55/0.57    spl4_30 <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k1_xboole_0)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.55/0.57  fof(f298,plain,(
% 1.55/0.57    ~r1_tarski(k1_xboole_0,k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2)) | k1_xboole_0 = k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2) | ~spl4_30),
% 1.55/0.57    inference(resolution,[],[f296,f50])).
% 1.55/0.57  fof(f50,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.55/0.57    inference(cnf_transformation,[],[f1])).
% 1.55/0.57  fof(f1,axiom,(
% 1.55/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.55/0.57  fof(f296,plain,(
% 1.55/0.57    r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k1_xboole_0) | ~spl4_30),
% 1.55/0.57    inference(avatar_component_clause,[],[f294])).
% 1.55/0.57  fof(f297,plain,(
% 1.55/0.57    spl4_30 | ~spl4_22 | ~spl4_24),
% 1.55/0.57    inference(avatar_split_clause,[],[f266,f237,f223,f294])).
% 1.55/0.57  fof(f223,plain,(
% 1.55/0.57    spl4_22 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.55/0.57  fof(f237,plain,(
% 1.55/0.57    spl4_24 <=> r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.55/0.57  fof(f266,plain,(
% 1.55/0.57    r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k1_xboole_0) | (~spl4_22 | ~spl4_24)),
% 1.55/0.57    inference(forward_demodulation,[],[f238,f225])).
% 1.55/0.57  fof(f225,plain,(
% 1.55/0.57    k1_xboole_0 = k2_relat_1(sK3) | ~spl4_22),
% 1.55/0.57    inference(avatar_component_clause,[],[f223])).
% 1.55/0.57  fof(f238,plain,(
% 1.55/0.57    r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) | ~spl4_24),
% 1.55/0.57    inference(avatar_component_clause,[],[f237])).
% 1.55/0.57  fof(f249,plain,(
% 1.55/0.57    ~spl4_5 | spl4_25),
% 1.55/0.57    inference(avatar_contradiction_clause,[],[f247])).
% 1.55/0.57  fof(f247,plain,(
% 1.55/0.57    $false | (~spl4_5 | spl4_25)),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f106,f245,f44])).
% 1.55/0.57  fof(f44,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f23])).
% 1.55/0.57  fof(f23,plain,(
% 1.55/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.55/0.57    inference(ennf_transformation,[],[f9])).
% 1.55/0.57  fof(f9,axiom,(
% 1.55/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 1.55/0.57  fof(f245,plain,(
% 1.55/0.57    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | spl4_25),
% 1.55/0.57    inference(avatar_component_clause,[],[f243])).
% 1.55/0.57  fof(f243,plain,(
% 1.55/0.57    spl4_25 <=> r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.55/0.57  fof(f106,plain,(
% 1.55/0.57    v1_relat_1(sK3) | ~spl4_5),
% 1.55/0.57    inference(avatar_component_clause,[],[f104])).
% 1.55/0.57  fof(f104,plain,(
% 1.55/0.57    spl4_5 <=> v1_relat_1(sK3)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.55/0.57  fof(f246,plain,(
% 1.55/0.57    ~spl4_15 | ~spl4_25 | spl4_24),
% 1.55/0.57    inference(avatar_split_clause,[],[f241,f237,f243,f165])).
% 1.55/0.57  fof(f165,plain,(
% 1.55/0.57    spl4_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.55/0.57  fof(f241,plain,(
% 1.55/0.57    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | spl4_24),
% 1.55/0.57    inference(superposition,[],[f239,f63])).
% 1.55/0.57  fof(f63,plain,(
% 1.55/0.57    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f33])).
% 1.55/0.57  fof(f33,plain,(
% 1.55/0.57    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.57    inference(ennf_transformation,[],[f15])).
% 1.55/0.57  fof(f15,axiom,(
% 1.55/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.55/0.57  fof(f239,plain,(
% 1.55/0.57    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) | spl4_24),
% 1.55/0.57    inference(avatar_component_clause,[],[f237])).
% 1.55/0.57  fof(f240,plain,(
% 1.55/0.57    ~spl4_24 | spl4_11 | ~spl4_13 | ~spl4_20),
% 1.55/0.57    inference(avatar_split_clause,[],[f234,f205,f147,f135,f237])).
% 1.55/0.57  fof(f135,plain,(
% 1.55/0.57    spl4_11 <=> r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.55/0.57  fof(f147,plain,(
% 1.55/0.57    spl4_13 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.55/0.57  fof(f205,plain,(
% 1.55/0.57    spl4_20 <=> k2_relat_1(sK3) = k11_relat_1(sK3,sK0)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.55/0.57  fof(f234,plain,(
% 1.55/0.57    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_relat_1(sK3)) | (spl4_11 | ~spl4_13 | ~spl4_20)),
% 1.55/0.57    inference(forward_demodulation,[],[f233,f149])).
% 1.55/0.57  fof(f149,plain,(
% 1.55/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~spl4_13),
% 1.55/0.57    inference(avatar_component_clause,[],[f147])).
% 1.55/0.57  fof(f233,plain,(
% 1.55/0.57    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_relat_1(sK3)) | (spl4_11 | ~spl4_20)),
% 1.55/0.57    inference(forward_demodulation,[],[f137,f207])).
% 1.55/0.57  fof(f207,plain,(
% 1.55/0.57    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~spl4_20),
% 1.55/0.57    inference(avatar_component_clause,[],[f205])).
% 1.55/0.57  fof(f137,plain,(
% 1.55/0.57    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0)) | spl4_11),
% 1.55/0.57    inference(avatar_component_clause,[],[f135])).
% 1.55/0.57  fof(f231,plain,(
% 1.55/0.57    spl4_10 | ~spl4_5 | spl4_22 | ~spl4_20),
% 1.55/0.57    inference(avatar_split_clause,[],[f209,f205,f223,f104,f131])).
% 1.55/0.57  fof(f131,plain,(
% 1.55/0.57    spl4_10 <=> r2_hidden(sK0,k1_relat_1(sK3))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.55/0.57  fof(f209,plain,(
% 1.55/0.57    k1_xboole_0 = k2_relat_1(sK3) | ~v1_relat_1(sK3) | r2_hidden(sK0,k1_relat_1(sK3)) | ~spl4_20),
% 1.55/0.57    inference(superposition,[],[f207,f45])).
% 1.55/0.57  fof(f45,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1) | r2_hidden(X0,k1_relat_1(X1))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f24])).
% 1.55/0.57  fof(f24,plain,(
% 1.55/0.57    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.55/0.57    inference(ennf_transformation,[],[f11])).
% 1.55/0.57  fof(f11,axiom,(
% 1.55/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 1.55/0.57  fof(f208,plain,(
% 1.55/0.57    ~spl4_5 | spl4_20 | ~spl4_13),
% 1.55/0.57    inference(avatar_split_clause,[],[f199,f147,f205,f104])).
% 1.55/0.57  fof(f199,plain,(
% 1.55/0.57    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_13),
% 1.55/0.57    inference(duplicate_literal_removal,[],[f196])).
% 1.55/0.57  fof(f196,plain,(
% 1.55/0.57    k2_relat_1(sK3) = k11_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_13),
% 1.55/0.57    inference(superposition,[],[f41,f158])).
% 1.55/0.57  fof(f158,plain,(
% 1.55/0.57    ( ! [X0] : (k11_relat_1(X0,sK0) = k9_relat_1(X0,k1_relat_1(sK3)) | ~v1_relat_1(X0)) ) | ~spl4_13),
% 1.55/0.57    inference(superposition,[],[f69,f149])).
% 1.55/0.57  fof(f69,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f42,f65])).
% 1.55/0.57  fof(f65,plain,(
% 1.55/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f40,f64])).
% 1.55/0.57  fof(f64,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f43,f53])).
% 1.55/0.57  fof(f53,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f4])).
% 1.55/0.57  fof(f4,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.55/0.57  fof(f43,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f3])).
% 1.55/0.57  fof(f3,axiom,(
% 1.55/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.55/0.57  fof(f40,plain,(
% 1.55/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f2])).
% 1.55/0.57  fof(f2,axiom,(
% 1.55/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.55/0.57  fof(f42,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f22])).
% 1.55/0.57  fof(f22,plain,(
% 1.55/0.57    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.55/0.57    inference(ennf_transformation,[],[f8])).
% 1.55/0.57  fof(f8,axiom,(
% 1.55/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.55/0.57  fof(f41,plain,(
% 1.55/0.57    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f21])).
% 1.55/0.57  fof(f21,plain,(
% 1.55/0.57    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.57    inference(ennf_transformation,[],[f10])).
% 1.55/0.57  fof(f10,axiom,(
% 1.55/0.57    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.55/0.57  fof(f194,plain,(
% 1.55/0.57    ~spl4_19 | spl4_6 | ~spl4_13),
% 1.55/0.57    inference(avatar_split_clause,[],[f154,f147,f109,f191])).
% 1.55/0.57  fof(f109,plain,(
% 1.55/0.57    spl4_6 <=> r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.55/0.57  fof(f154,plain,(
% 1.55/0.57    ~r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | (spl4_6 | ~spl4_13)),
% 1.55/0.57    inference(backward_demodulation,[],[f111,f149])).
% 1.55/0.57  fof(f111,plain,(
% 1.55/0.57    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) | spl4_6),
% 1.55/0.57    inference(avatar_component_clause,[],[f109])).
% 1.55/0.57  fof(f168,plain,(
% 1.55/0.57    spl4_15 | ~spl4_4 | ~spl4_13),
% 1.55/0.57    inference(avatar_split_clause,[],[f152,f147,f94,f165])).
% 1.55/0.57  fof(f94,plain,(
% 1.55/0.57    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.55/0.57  fof(f152,plain,(
% 1.55/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) | (~spl4_4 | ~spl4_13)),
% 1.55/0.57    inference(backward_demodulation,[],[f96,f149])).
% 1.55/0.57  fof(f96,plain,(
% 1.55/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl4_4),
% 1.55/0.57    inference(avatar_component_clause,[],[f94])).
% 1.55/0.57  fof(f150,plain,(
% 1.55/0.57    ~spl4_4 | spl4_13 | ~spl4_12),
% 1.55/0.57    inference(avatar_split_clause,[],[f144,f140,f147,f94])).
% 1.55/0.57  fof(f140,plain,(
% 1.55/0.57    spl4_12 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.55/0.57  fof(f144,plain,(
% 1.55/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl4_12),
% 1.55/0.57    inference(superposition,[],[f142,f55])).
% 1.55/0.57  fof(f55,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f28])).
% 1.55/0.57  fof(f28,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.57    inference(ennf_transformation,[],[f14])).
% 1.55/0.57  fof(f14,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.55/0.57  fof(f142,plain,(
% 1.55/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) | ~spl4_12),
% 1.55/0.57    inference(avatar_component_clause,[],[f140])).
% 1.55/0.57  fof(f143,plain,(
% 1.55/0.57    ~spl4_3 | spl4_12 | spl4_2 | ~spl4_4),
% 1.55/0.57    inference(avatar_split_clause,[],[f99,f94,f84,f140,f89])).
% 1.55/0.57  fof(f89,plain,(
% 1.55/0.57    spl4_3 <=> v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.55/0.57  fof(f84,plain,(
% 1.55/0.57    spl4_2 <=> k1_xboole_0 = sK1),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.55/0.57  fof(f99,plain,(
% 1.55/0.57    k1_xboole_0 = sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) | ~v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl4_4),
% 1.55/0.57    inference(resolution,[],[f96,f61])).
% 1.55/0.57  fof(f61,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f30])).
% 1.55/0.57  fof(f30,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.57    inference(flattening,[],[f29])).
% 1.55/0.57  fof(f29,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.57    inference(ennf_transformation,[],[f16])).
% 1.55/0.57  fof(f16,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.55/0.57  fof(f138,plain,(
% 1.55/0.57    ~spl4_5 | ~spl4_10 | ~spl4_1 | ~spl4_11 | spl4_6),
% 1.55/0.57    inference(avatar_split_clause,[],[f129,f109,f135,f79,f131,f104])).
% 1.55/0.57  fof(f79,plain,(
% 1.55/0.57    spl4_1 <=> v1_funct_1(sK3)),
% 1.55/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.55/0.57  fof(f129,plain,(
% 1.55/0.57    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k11_relat_1(sK3,sK0)) | ~v1_funct_1(sK3) | ~r2_hidden(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_6),
% 1.55/0.57    inference(superposition,[],[f111,f70])).
% 1.55/0.57  fof(f70,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k11_relat_1(X1,X0) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f47,f65])).
% 1.55/0.57  fof(f47,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f26])).
% 1.55/0.57  fof(f26,plain,(
% 1.55/0.57    ! [X0,X1] : (k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.55/0.57    inference(flattening,[],[f25])).
% 1.55/0.57  fof(f25,plain,(
% 1.55/0.57    ! [X0,X1] : ((k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.55/0.57    inference(ennf_transformation,[],[f12])).
% 1.55/0.57  fof(f12,axiom,(
% 1.55/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 1.55/0.57  fof(f112,plain,(
% 1.55/0.57    ~spl4_6),
% 1.55/0.57    inference(avatar_split_clause,[],[f66,f109])).
% 1.55/0.57  fof(f66,plain,(
% 1.55/0.57    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 1.55/0.57    inference(definition_unfolding,[],[f38,f65,f65])).
% 1.55/0.57  fof(f38,plain,(
% 1.55/0.57    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.55/0.57    inference(cnf_transformation,[],[f20])).
% 1.55/0.57  fof(f20,plain,(
% 1.55/0.57    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 1.55/0.57    inference(flattening,[],[f19])).
% 1.55/0.57  fof(f19,plain,(
% 1.55/0.57    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 1.55/0.57    inference(ennf_transformation,[],[f18])).
% 1.55/0.57  fof(f18,negated_conjecture,(
% 1.55/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.55/0.57    inference(negated_conjecture,[],[f17])).
% 1.55/0.57  fof(f17,conjecture,(
% 1.55/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).
% 1.55/0.57  fof(f107,plain,(
% 1.55/0.57    spl4_5 | ~spl4_4),
% 1.55/0.57    inference(avatar_split_clause,[],[f100,f94,f104])).
% 1.55/0.57  fof(f100,plain,(
% 1.55/0.57    v1_relat_1(sK3) | ~spl4_4),
% 1.55/0.57    inference(resolution,[],[f96,f54])).
% 1.55/0.57  fof(f54,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.55/0.57    inference(cnf_transformation,[],[f27])).
% 1.55/0.57  fof(f27,plain,(
% 1.55/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.55/0.57    inference(ennf_transformation,[],[f13])).
% 1.55/0.57  fof(f13,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.55/0.57  fof(f97,plain,(
% 1.55/0.57    spl4_4),
% 1.55/0.57    inference(avatar_split_clause,[],[f67,f94])).
% 1.55/0.57  fof(f67,plain,(
% 1.55/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.55/0.57    inference(definition_unfolding,[],[f36,f65])).
% 1.55/0.57  fof(f36,plain,(
% 1.55/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.55/0.57    inference(cnf_transformation,[],[f20])).
% 1.55/0.57  fof(f92,plain,(
% 1.55/0.57    spl4_3),
% 1.55/0.57    inference(avatar_split_clause,[],[f68,f89])).
% 1.55/0.57  fof(f68,plain,(
% 1.55/0.57    v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.55/0.57    inference(definition_unfolding,[],[f35,f65])).
% 1.55/0.57  fof(f35,plain,(
% 1.55/0.57    v1_funct_2(sK3,k1_tarski(sK0),sK1)),
% 1.55/0.57    inference(cnf_transformation,[],[f20])).
% 1.55/0.57  fof(f87,plain,(
% 1.55/0.57    ~spl4_2),
% 1.55/0.57    inference(avatar_split_clause,[],[f37,f84])).
% 1.55/0.57  fof(f37,plain,(
% 1.55/0.57    k1_xboole_0 != sK1),
% 1.55/0.57    inference(cnf_transformation,[],[f20])).
% 1.55/0.57  fof(f82,plain,(
% 1.55/0.57    spl4_1),
% 1.55/0.57    inference(avatar_split_clause,[],[f34,f79])).
% 1.55/0.57  fof(f34,plain,(
% 1.55/0.57    v1_funct_1(sK3)),
% 1.55/0.57    inference(cnf_transformation,[],[f20])).
% 1.55/0.57  % SZS output end Proof for theBenchmark
% 1.55/0.57  % (31291)------------------------------
% 1.55/0.57  % (31291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (31291)Termination reason: Refutation
% 1.55/0.57  
% 1.55/0.57  % (31291)Memory used [KB]: 10874
% 1.55/0.57  % (31291)Time elapsed: 0.135 s
% 1.55/0.57  % (31291)------------------------------
% 1.55/0.57  % (31291)------------------------------
% 1.55/0.57  % (31264)Refutation not found, incomplete strategy% (31264)------------------------------
% 1.55/0.57  % (31264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (31264)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (31264)Memory used [KB]: 1791
% 1.55/0.57  % (31264)Time elapsed: 0.149 s
% 1.55/0.57  % (31264)------------------------------
% 1.55/0.57  % (31264)------------------------------
% 1.55/0.58  % (31262)Success in time 0.211 s
%------------------------------------------------------------------------------
