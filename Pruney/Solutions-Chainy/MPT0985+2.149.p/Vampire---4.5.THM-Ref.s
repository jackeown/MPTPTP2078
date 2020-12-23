%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 275 expanded)
%              Number of leaves         :   37 ( 127 expanded)
%              Depth                    :    9
%              Number of atoms          :  447 ( 901 expanded)
%              Number of equality atoms :   59 ( 127 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (4370)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
fof(f389,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f101,f109,f118,f135,f140,f150,f156,f169,f177,f182,f187,f203,f214,f215,f287,f369,f381,f387,f388])).

fof(f388,plain,
    ( k2_funct_1(sK2) != k4_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f387,plain,
    ( spl3_40
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_21
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f382,f366,f205,f179,f174,f105,f384])).

fof(f384,plain,
    ( spl3_40
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f105,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f174,plain,
    ( spl3_17
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f179,plain,
    ( spl3_18
  <=> v1_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f205,plain,
    ( spl3_21
  <=> sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f366,plain,
    ( spl3_39
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f382,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_21
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f378,f207])).

fof(f207,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f205])).

fof(f378,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),sK0)))
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(unit_resulting_resolution,[],[f106,f176,f181,f368,f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k4_relat_1(X0))
      | m1_subset_1(k4_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(X0)),X1)))
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f61,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f368,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f366])).

fof(f181,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f179])).

fof(f176,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f174])).

fof(f106,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f381,plain,
    ( spl3_19
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_21
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f380,f366,f205,f179,f174,f105,f184])).

fof(f184,plain,
    ( spl3_19
  <=> v1_funct_2(k4_relat_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f380,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_21
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f379,f207])).

fof(f379,plain,
    ( v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),sK0)
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_39 ),
    inference(unit_resulting_resolution,[],[f106,f176,f181,f368,f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k4_relat_1(X0))
      | v1_funct_2(k4_relat_1(X0),k1_relat_1(k4_relat_1(X0)),X1)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f60,f55])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f369,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | ~ spl3_5
    | spl3_39
    | ~ spl3_22
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f364,f284,f209,f366,f83,f98,f105])).

fof(f98,plain,
    ( spl3_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f83,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f209,plain,
    ( spl3_22
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f284,plain,
    ( spl3_31
  <=> sK1 = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f364,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_22
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f363,f211])).

fof(f211,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f209])).

fof(f363,plain,
    ( r1_tarski(k10_relat_1(sK2,sK1),sK0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_31 ),
    inference(superposition,[],[f57,f286])).

fof(f286,plain,
    ( sK1 = k9_relat_1(sK2,sK0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f284])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f287,plain,
    ( spl3_31
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f282,f198,f153,f105,f284])).

fof(f153,plain,
    ( spl3_15
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f198,plain,
    ( spl3_20
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f282,plain,
    ( sK1 = k9_relat_1(sK2,sK0)
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f279,f200])).

fof(f200,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f279,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f155,f106,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f155,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f153])).

fof(f215,plain,
    ( spl3_22
    | ~ spl3_14
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f213,f198,f147,f209])).

fof(f147,plain,
    ( spl3_14
  <=> k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f213,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl3_14
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f149,f200])).

fof(f149,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f214,plain,
    ( spl3_21
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f212,f198,f137,f205])).

fof(f137,plain,
    ( spl3_12
  <=> k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f212,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f139,f200])).

fof(f139,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f203,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f202,f88,f78,f198])).

fof(f78,plain,
    ( spl3_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f88,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f202,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f195,f80])).

fof(f80,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f195,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f51,f90])).

fof(f90,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f187,plain,
    ( ~ spl3_19
    | spl3_2
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f172,f165,f69,f184])).

fof(f69,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f165,plain,
    ( spl3_16
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f172,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | spl3_2
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f71,f167])).

fof(f167,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f71,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f182,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f171,f165,f65,f179])).

fof(f65,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f171,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f66,f167])).

fof(f66,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f177,plain,
    ( spl3_17
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f170,f165,f132,f174])).

fof(f132,plain,
    ( spl3_11
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f170,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f134,f167])).

fof(f134,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f169,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | spl3_16
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f163,f83,f165,f98,f105])).

fof(f163,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f48,f85])).

fof(f85,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f156,plain,
    ( spl3_15
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f151,f88,f153])).

fof(f151,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f150,plain,
    ( spl3_14
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f126,f105,f147])).

fof(f126,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f106,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f140,plain,
    ( spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f128,f105,f137])).

fof(f128,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f106,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f135,plain,
    ( spl3_11
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f130,f105,f98,f132])).

fof(f130,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f100,f106,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f100,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f118,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f114,f88,f105])).

fof(f114,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f63,f90,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f109,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | spl3_1 ),
    inference(avatar_split_clause,[],[f103,f65,f98,f105])).

fof(f103,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f50,f67])).

fof(f67,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f101,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f40,f98])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f38])).

fof(f38,plain,
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

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f91,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f42,f88])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f43,f83])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f44,f78])).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f73,f69,f65])).

fof(f73,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f45,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:09:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (4378)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (4386)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (4375)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.52  % (4383)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (4392)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (4377)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (4387)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.53  % (4391)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (4374)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.53  % (4384)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.53  % (4376)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.53  % (4379)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (4393)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.53  % (4371)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.53  % (4385)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.53  % (4377)Refutation not found, incomplete strategy% (4377)------------------------------
% 0.21/0.53  % (4377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4377)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4377)Memory used [KB]: 6268
% 0.21/0.53  % (4377)Time elapsed: 0.100 s
% 0.21/0.53  % (4377)------------------------------
% 0.21/0.53  % (4377)------------------------------
% 0.21/0.53  % (4376)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (4372)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.53  % (4373)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.53  % (4382)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (4390)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.54  % (4389)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.54  % (4393)Refutation not found, incomplete strategy% (4393)------------------------------
% 0.21/0.54  % (4393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4393)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4393)Memory used [KB]: 10618
% 0.21/0.54  % (4393)Time elapsed: 0.112 s
% 0.21/0.54  % (4393)------------------------------
% 0.21/0.54  % (4393)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  % (4370)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.54  fof(f389,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f101,f109,f118,f135,f140,f150,f156,f169,f177,f182,f187,f203,f214,f215,f287,f369,f381,f387,f388])).
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    k2_funct_1(sK2) != k4_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f387,plain,(
% 0.21/0.54    spl3_40 | ~spl3_9 | ~spl3_17 | ~spl3_18 | ~spl3_21 | ~spl3_39),
% 0.21/0.54    inference(avatar_split_clause,[],[f382,f366,f205,f179,f174,f105,f384])).
% 0.21/0.54  fof(f384,plain,(
% 0.21/0.54    spl3_40 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl3_9 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    spl3_17 <=> v1_relat_1(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    spl3_18 <=> v1_funct_1(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    spl3_21 <=> sK1 = k1_relat_1(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    spl3_39 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.54  fof(f382,plain,(
% 0.21/0.54    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_9 | ~spl3_17 | ~spl3_18 | ~spl3_21 | ~spl3_39)),
% 0.21/0.54    inference(forward_demodulation,[],[f378,f207])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    sK1 = k1_relat_1(k4_relat_1(sK2)) | ~spl3_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f205])).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),sK0))) | (~spl3_9 | ~spl3_17 | ~spl3_18 | ~spl3_39)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f106,f176,f181,f368,f225])).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_1(k4_relat_1(X0)) | m1_subset_1(k4_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(X0)),X1))) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(superposition,[],[f61,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.54  fof(f368,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_39),
% 0.21/0.54    inference(avatar_component_clause,[],[f366])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    v1_funct_1(k4_relat_1(sK2)) | ~spl3_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f179])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(sK2)) | ~spl3_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f174])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl3_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f105])).
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    spl3_19 | ~spl3_9 | ~spl3_17 | ~spl3_18 | ~spl3_21 | ~spl3_39),
% 0.21/0.54    inference(avatar_split_clause,[],[f380,f366,f205,f179,f174,f105,f184])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    spl3_19 <=> v1_funct_2(k4_relat_1(sK2),sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.54  fof(f380,plain,(
% 0.21/0.54    v1_funct_2(k4_relat_1(sK2),sK1,sK0) | (~spl3_9 | ~spl3_17 | ~spl3_18 | ~spl3_21 | ~spl3_39)),
% 0.21/0.54    inference(forward_demodulation,[],[f379,f207])).
% 0.21/0.54  fof(f379,plain,(
% 0.21/0.54    v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),sK0) | (~spl3_9 | ~spl3_17 | ~spl3_18 | ~spl3_39)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f106,f176,f181,f368,f223])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_1(k4_relat_1(X0)) | v1_funct_2(k4_relat_1(X0),k1_relat_1(k4_relat_1(X0)),X1) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(superposition,[],[f60,f55])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f369,plain,(
% 0.21/0.54    ~spl3_9 | ~spl3_8 | ~spl3_5 | spl3_39 | ~spl3_22 | ~spl3_31),
% 0.21/0.54    inference(avatar_split_clause,[],[f364,f284,f209,f366,f83,f98,f105])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl3_8 <=> v1_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    spl3_5 <=> v2_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    spl3_22 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.54  fof(f284,plain,(
% 0.21/0.54    spl3_31 <=> sK1 = k9_relat_1(sK2,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.54  fof(f364,plain,(
% 0.21/0.54    r1_tarski(k1_relat_1(sK2),sK0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_22 | ~spl3_31)),
% 0.21/0.54    inference(forward_demodulation,[],[f363,f211])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~spl3_22),
% 0.21/0.54    inference(avatar_component_clause,[],[f209])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    r1_tarski(k10_relat_1(sK2,sK1),sK0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_31),
% 0.21/0.54    inference(superposition,[],[f57,f286])).
% 0.21/0.54  fof(f286,plain,(
% 0.21/0.54    sK1 = k9_relat_1(sK2,sK0) | ~spl3_31),
% 0.21/0.54    inference(avatar_component_clause,[],[f284])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 0.21/0.54  fof(f287,plain,(
% 0.21/0.54    spl3_31 | ~spl3_9 | ~spl3_15 | ~spl3_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f282,f198,f153,f105,f284])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    spl3_15 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    spl3_20 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.54  fof(f282,plain,(
% 0.21/0.54    sK1 = k9_relat_1(sK2,sK0) | (~spl3_9 | ~spl3_15 | ~spl3_20)),
% 0.21/0.54    inference(forward_demodulation,[],[f279,f200])).
% 0.21/0.54  fof(f200,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2) | ~spl3_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f198])).
% 0.21/0.54  fof(f279,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | (~spl3_9 | ~spl3_15)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f155,f106,f161])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f159])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(superposition,[],[f53,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    v4_relat_1(sK2,sK0) | ~spl3_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f153])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    spl3_22 | ~spl3_14 | ~spl3_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f213,f198,f147,f209])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    spl3_14 <=> k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | (~spl3_14 | ~spl3_20)),
% 0.21/0.54    inference(backward_demodulation,[],[f149,f200])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) | ~spl3_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f147])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    spl3_21 | ~spl3_12 | ~spl3_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f212,f198,f137,f205])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    spl3_12 <=> k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    sK1 = k1_relat_1(k4_relat_1(sK2)) | (~spl3_12 | ~spl3_20)),
% 0.21/0.54    inference(backward_demodulation,[],[f139,f200])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | ~spl3_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f137])).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    spl3_20 | ~spl3_4 | ~spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f202,f88,f78,f198])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl3_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.54  fof(f202,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2) | (~spl3_4 | ~spl3_6)),
% 0.21/0.54    inference(forward_demodulation,[],[f195,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f78])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_6),
% 0.21/0.54    inference(resolution,[],[f51,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f88])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ~spl3_19 | spl3_2 | ~spl3_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f172,f165,f69,f184])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    spl3_16 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | (spl3_2 | ~spl3_16)),
% 0.21/0.54    inference(backward_demodulation,[],[f71,f167])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl3_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f165])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f69])).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    spl3_18 | ~spl3_1 | ~spl3_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f171,f165,f65,f179])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    v1_funct_1(k4_relat_1(sK2)) | (~spl3_1 | ~spl3_16)),
% 0.21/0.54    inference(backward_demodulation,[],[f66,f167])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f65])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    spl3_17 | ~spl3_11 | ~spl3_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f170,f165,f132,f174])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl3_11 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    v1_relat_1(k4_relat_1(sK2)) | (~spl3_11 | ~spl3_16)),
% 0.21/0.54    inference(backward_demodulation,[],[f134,f167])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    v1_relat_1(k2_funct_1(sK2)) | ~spl3_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f132])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    ~spl3_9 | ~spl3_8 | spl3_16 | ~spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f163,f83,f165,f98,f105])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.21/0.54    inference(resolution,[],[f48,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    v2_funct_1(sK2) | ~spl3_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f83])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    spl3_15 | ~spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f151,f88,f153])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    v4_relat_1(sK2,sK0) | ~spl3_6),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f90,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    spl3_14 | ~spl3_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f126,f105,f147])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) | ~spl3_9),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f106,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    spl3_12 | ~spl3_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f128,f105,f137])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | ~spl3_9),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f106,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    spl3_11 | ~spl3_8 | ~spl3_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f130,f105,f98,f132])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    v1_relat_1(k2_funct_1(sK2)) | (~spl3_8 | ~spl3_9)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f100,f106,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    v1_funct_1(sK2) | ~spl3_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f98])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    spl3_9 | ~spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f114,f88,f105])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl3_6),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f63,f90,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ~spl3_9 | ~spl3_8 | spl3_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f103,f65,f98,f105])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.21/0.54    inference(resolution,[],[f50,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f65])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl3_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f98])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f15])).
% 0.21/0.54  fof(f15,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    spl3_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f88])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl3_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f83])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    v2_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    spl3_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f78])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f73,f69,f65])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (4376)------------------------------
% 0.21/0.54  % (4376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4376)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (4376)Memory used [KB]: 10874
% 0.21/0.54  % (4376)Time elapsed: 0.105 s
% 0.21/0.54  % (4376)------------------------------
% 0.21/0.54  % (4376)------------------------------
% 0.21/0.54  % (4369)Success in time 0.176 s
%------------------------------------------------------------------------------
