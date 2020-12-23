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
% DateTime   : Thu Dec  3 13:02:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 297 expanded)
%              Number of leaves         :   42 ( 126 expanded)
%              Depth                    :    9
%              Number of atoms          :  520 ( 951 expanded)
%              Number of equality atoms :  127 ( 218 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f809,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f125,f144,f150,f155,f179,f193,f205,f212,f237,f261,f274,f304,f337,f362,f448,f450,f458,f533,f553,f599,f620,f630,f662,f746,f749,f807,f808])).

fof(f808,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f807,plain,
    ( spl3_38
    | ~ spl3_57 ),
    inference(avatar_contradiction_clause,[],[f806])).

fof(f806,plain,
    ( $false
    | spl3_38
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f793,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f793,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_38
    | ~ spl3_57 ),
    inference(superposition,[],[f558,f745])).

fof(f745,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f743])).

fof(f743,plain,
    ( spl3_57
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f558,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl3_38
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f749,plain,
    ( k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | k1_xboole_0 != sK2
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != sK0
    | sK1 != k2_relat_1(sK2)
    | k1_xboole_0 != sK1
    | sK0 = k1_relat_1(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f746,plain,
    ( spl3_57
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f736,f301,f297,f271,f228,f743])).

fof(f228,plain,
    ( spl3_15
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f271,plain,
    ( spl3_19
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f297,plain,
    ( spl3_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f301,plain,
    ( spl3_22
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f736,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f735,f299])).

fof(f299,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f297])).

fof(f735,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f277,f302])).

fof(f302,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f301])).

fof(f277,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f275,f229])).

fof(f229,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f228])).

fof(f275,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_19 ),
    inference(superposition,[],[f82,f273])).

fof(f273,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f271])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f662,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f630,plain,
    ( ~ spl3_30
    | ~ spl3_38
    | spl3_42 ),
    inference(avatar_contradiction_clause,[],[f629])).

fof(f629,plain,
    ( $false
    | ~ spl3_30
    | ~ spl3_38
    | spl3_42 ),
    inference(subsumption_resolution,[],[f602,f385])).

fof(f385,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl3_30
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f602,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_38
    | spl3_42 ),
    inference(subsumption_resolution,[],[f601,f559])).

fof(f559,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f557])).

fof(f601,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_42 ),
    inference(superposition,[],[f594,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f594,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl3_42
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

% (15726)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (15723)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (15736)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (15724)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f620,plain,
    ( ~ spl3_45
    | ~ spl3_21
    | spl3_35 ),
    inference(avatar_split_clause,[],[f536,f445,f297,f617])).

fof(f617,plain,
    ( spl3_45
  <=> sK0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f445,plain,
    ( spl3_35
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f536,plain,
    ( sK0 != k1_relat_1(k1_xboole_0)
    | ~ spl3_21
    | spl3_35 ),
    inference(forward_demodulation,[],[f446,f299])).

fof(f446,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl3_35 ),
    inference(avatar_component_clause,[],[f445])).

fof(f599,plain,
    ( spl3_41
    | ~ spl3_42
    | spl3_43
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f579,f557,f596,f592,f588])).

fof(f588,plain,
    ( spl3_41
  <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f596,plain,
    ( spl3_43
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f579,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ spl3_38 ),
    inference(resolution,[],[f559,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f553,plain,
    ( sK0 != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f533,plain,
    ( sK0 != k1_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f458,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_4
    | spl3_28 ),
    inference(avatar_split_clause,[],[f456,f374,f147,f141,f301])).

fof(f141,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f147,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f374,plain,
    ( spl3_28
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f456,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_28 ),
    inference(subsumption_resolution,[],[f398,f375])).

fof(f375,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f374])).

fof(f398,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f145,f149])).

fof(f149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f145,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_3 ),
    inference(resolution,[],[f143,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f143,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f141])).

fof(f450,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f448,plain,
    ( spl3_35
    | ~ spl3_4
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f431,f374,f147,f445])).

fof(f431,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f429,f149])).

fof(f429,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_28 ),
    inference(superposition,[],[f376,f100])).

fof(f376,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f374])).

fof(f362,plain,
    ( spl3_26
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f356,f271,f258,f228,f176,f359])).

fof(f359,plain,
    ( spl3_26
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f176,plain,
    ( spl3_9
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f258,plain,
    ( spl3_18
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f356,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f355,f273])).

fof(f355,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f354,f260])).

fof(f260,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f258])).

fof(f354,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f221,f229])).

fof(f221,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_9 ),
    inference(resolution,[],[f177,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f177,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f176])).

fof(f337,plain,
    ( spl3_24
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f332,f271,f258,f228,f176,f334])).

fof(f334,plain,
    ( spl3_24
  <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f332,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f331,f273])).

fof(f331,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f330,f260])).

fof(f330,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f220,f229])).

fof(f220,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_9 ),
    inference(resolution,[],[f177,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f304,plain,
    ( spl3_21
    | ~ spl3_22
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f293,f202,f190,f301,f297])).

fof(f190,plain,
    ( spl3_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f202,plain,
    ( spl3_13
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f293,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f208,f191])).

fof(f191,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f190])).

fof(f208,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_13 ),
    inference(superposition,[],[f83,f204])).

fof(f204,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f202])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f274,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f269,f202,f190,f122,f117,f271])).

fof(f117,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f122,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f269,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f214,f191])).

fof(f214,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f138,f204])).

fof(f138,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f134,f119])).

fof(f119,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f134,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f124,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f124,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f261,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f256,f190,f122,f117,f258])).

fof(f256,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f139,f191])).

fof(f139,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f135,f119])).

fof(f135,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f124,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f237,plain,
    ( ~ spl3_1
    | ~ spl3_11
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_11
    | spl3_15 ),
    inference(subsumption_resolution,[],[f235,f191])).

fof(f235,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_15 ),
    inference(subsumption_resolution,[],[f232,f119])).

fof(f232,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_15 ),
    inference(resolution,[],[f230,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f230,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f228])).

fof(f212,plain,
    ( ~ spl3_4
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl3_4
    | spl3_11 ),
    inference(resolution,[],[f194,f149])).

fof(f194,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_11 ),
    inference(resolution,[],[f192,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f192,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f190])).

fof(f205,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f160,f152,f147,f202])).

fof(f152,plain,
    ( spl3_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f160,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f158,f149])).

fof(f158,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_5 ),
    inference(superposition,[],[f154,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f154,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f193,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | spl3_9 ),
    inference(avatar_split_clause,[],[f188,f176,f117,f190])).

fof(f188,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_9 ),
    inference(subsumption_resolution,[],[f129,f178])).

fof(f178,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f176])).

fof(f129,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f119,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f179,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f64,f176,f172,f168])).

fof(f168,plain,
    ( spl3_7
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f172,plain,
    ( spl3_8
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f64,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f155,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f69,f152])).

fof(f69,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f150,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f67,f147])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f144,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f66,f141])).

fof(f66,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f125,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f68,f122])).

fof(f68,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f120,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f65,f117])).

% (15738)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (15729)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.47  % (15730)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (15721)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (15728)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (15718)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (15722)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (15727)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (15720)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (15721)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (15733)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (15735)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (15725)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (15719)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f809,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f120,f125,f144,f150,f155,f179,f193,f205,f212,f237,f261,f274,f304,f337,f362,f448,f450,f458,f533,f553,f599,f620,f630,f662,f746,f749,f807,f808])).
% 0.22/0.50  fof(f808,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | k1_xboole_0 != sK1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f807,plain,(
% 0.22/0.50    spl3_38 | ~spl3_57),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f806])).
% 0.22/0.50  fof(f806,plain,(
% 0.22/0.50    $false | (spl3_38 | ~spl3_57)),
% 0.22/0.50    inference(subsumption_resolution,[],[f793,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.50  fof(f793,plain,(
% 0.22/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_38 | ~spl3_57)),
% 0.22/0.50    inference(superposition,[],[f558,f745])).
% 0.22/0.50  fof(f745,plain,(
% 0.22/0.50    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl3_57),
% 0.22/0.50    inference(avatar_component_clause,[],[f743])).
% 0.22/0.50  fof(f743,plain,(
% 0.22/0.50    spl3_57 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.22/0.50  fof(f558,plain,(
% 0.22/0.50    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f557])).
% 0.22/0.50  fof(f557,plain,(
% 0.22/0.50    spl3_38 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.50  fof(f749,plain,(
% 0.22/0.50    k1_xboole_0 != k2_funct_1(k1_xboole_0) | k1_xboole_0 != sK2 | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | k1_xboole_0 != sK0 | sK1 != k2_relat_1(sK2) | k1_xboole_0 != sK1 | sK0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f746,plain,(
% 0.22/0.50    spl3_57 | ~spl3_15 | ~spl3_19 | ~spl3_21 | ~spl3_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f736,f301,f297,f271,f228,f743])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    spl3_15 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    spl3_19 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    spl3_21 <=> k1_xboole_0 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    spl3_22 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.50  fof(f736,plain,(
% 0.22/0.50    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_15 | ~spl3_19 | ~spl3_21 | ~spl3_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f735,f299])).
% 0.22/0.50  fof(f299,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~spl3_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f297])).
% 0.22/0.50  fof(f735,plain,(
% 0.22/0.50    k1_xboole_0 = k2_funct_1(sK2) | (~spl3_15 | ~spl3_19 | ~spl3_22)),
% 0.22/0.50    inference(subsumption_resolution,[],[f277,f302])).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl3_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f301])).
% 0.22/0.50  fof(f277,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | k1_xboole_0 = k2_funct_1(sK2) | (~spl3_15 | ~spl3_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f275,f229])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    v1_relat_1(k2_funct_1(sK2)) | ~spl3_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f228])).
% 0.22/0.50  fof(f275,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2) | ~spl3_19),
% 0.22/0.50    inference(superposition,[],[f82,f273])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f271])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.50  fof(f662,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | k1_xboole_0 != sK1 | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f630,plain,(
% 0.22/0.50    ~spl3_30 | ~spl3_38 | spl3_42),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f629])).
% 0.22/0.50  fof(f629,plain,(
% 0.22/0.50    $false | (~spl3_30 | ~spl3_38 | spl3_42)),
% 0.22/0.50    inference(subsumption_resolution,[],[f602,f385])).
% 0.22/0.50  fof(f385,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl3_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f383])).
% 0.22/0.50  fof(f383,plain,(
% 0.22/0.50    spl3_30 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.50  fof(f602,plain,(
% 0.22/0.50    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl3_38 | spl3_42)),
% 0.22/0.50    inference(subsumption_resolution,[],[f601,f559])).
% 0.22/0.50  fof(f559,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl3_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f557])).
% 0.22/0.50  fof(f601,plain,(
% 0.22/0.50    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_42),
% 0.22/0.50    inference(superposition,[],[f594,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f594,plain,(
% 0.22/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | spl3_42),
% 0.22/0.50    inference(avatar_component_clause,[],[f592])).
% 0.22/0.50  fof(f592,plain,(
% 0.22/0.50    spl3_42 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.22/0.50  % (15726)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (15723)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (15736)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (15724)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  fof(f620,plain,(
% 0.22/0.51    ~spl3_45 | ~spl3_21 | spl3_35),
% 0.22/0.51    inference(avatar_split_clause,[],[f536,f445,f297,f617])).
% 0.22/0.51  fof(f617,plain,(
% 0.22/0.51    spl3_45 <=> sK0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.22/0.51  fof(f445,plain,(
% 0.22/0.51    spl3_35 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.51  fof(f536,plain,(
% 0.22/0.51    sK0 != k1_relat_1(k1_xboole_0) | (~spl3_21 | spl3_35)),
% 0.22/0.51    inference(forward_demodulation,[],[f446,f299])).
% 0.22/0.51  fof(f446,plain,(
% 0.22/0.51    sK0 != k1_relat_1(sK2) | spl3_35),
% 0.22/0.51    inference(avatar_component_clause,[],[f445])).
% 0.22/0.51  fof(f599,plain,(
% 0.22/0.51    spl3_41 | ~spl3_42 | spl3_43 | ~spl3_38),
% 0.22/0.51    inference(avatar_split_clause,[],[f579,f557,f596,f592,f588])).
% 0.22/0.51  fof(f588,plain,(
% 0.22/0.51    spl3_41 <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.51  fof(f596,plain,(
% 0.22/0.51    spl3_43 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.22/0.51  fof(f579,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | ~spl3_38),
% 0.22/0.51    inference(resolution,[],[f559,f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.51  fof(f553,plain,(
% 0.22/0.51    sK0 != k1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f533,plain,(
% 0.22/0.51    sK0 != k1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f458,plain,(
% 0.22/0.51    spl3_22 | ~spl3_3 | ~spl3_4 | spl3_28),
% 0.22/0.51    inference(avatar_split_clause,[],[f456,f374,f147,f141,f301])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    spl3_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f374,plain,(
% 0.22/0.51    spl3_28 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.51  fof(f456,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | (~spl3_3 | ~spl3_4 | spl3_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f398,f375])).
% 0.22/0.51  fof(f375,plain,(
% 0.22/0.51    sK0 != k1_relset_1(sK0,sK1,sK2) | spl3_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f374])).
% 0.22/0.51  fof(f398,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl3_3 | ~spl3_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f145,f149])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f147])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_3),
% 0.22/0.51    inference(resolution,[],[f143,f109])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f61])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f141])).
% 0.22/0.51  fof(f450,plain,(
% 0.22/0.51    k1_xboole_0 != sK2 | sK1 != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f448,plain,(
% 0.22/0.51    spl3_35 | ~spl3_4 | ~spl3_28),
% 0.22/0.51    inference(avatar_split_clause,[],[f431,f374,f147,f445])).
% 0.22/0.51  fof(f431,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK2) | (~spl3_4 | ~spl3_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f429,f149])).
% 0.22/0.51  fof(f429,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_28),
% 0.22/0.51    inference(superposition,[],[f376,f100])).
% 0.22/0.51  fof(f376,plain,(
% 0.22/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f374])).
% 0.22/0.51  fof(f362,plain,(
% 0.22/0.51    spl3_26 | ~spl3_9 | ~spl3_15 | ~spl3_18 | ~spl3_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f356,f271,f258,f228,f176,f359])).
% 0.22/0.51  fof(f359,plain,(
% 0.22/0.51    spl3_26 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    spl3_9 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.51  fof(f258,plain,(
% 0.22/0.51    spl3_18 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.51  fof(f356,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl3_9 | ~spl3_15 | ~spl3_18 | ~spl3_19)),
% 0.22/0.51    inference(forward_demodulation,[],[f355,f273])).
% 0.22/0.51  fof(f355,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl3_9 | ~spl3_15 | ~spl3_18)),
% 0.22/0.51    inference(forward_demodulation,[],[f354,f260])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f258])).
% 0.22/0.51  fof(f354,plain,(
% 0.22/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl3_9 | ~spl3_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f221,f229])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_9),
% 0.22/0.51    inference(resolution,[],[f177,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    v1_funct_1(k2_funct_1(sK2)) | ~spl3_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f176])).
% 0.22/0.51  fof(f337,plain,(
% 0.22/0.51    spl3_24 | ~spl3_9 | ~spl3_15 | ~spl3_18 | ~spl3_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f332,f271,f258,f228,f176,f334])).
% 0.22/0.51  fof(f334,plain,(
% 0.22/0.51    spl3_24 <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.51  fof(f332,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl3_9 | ~spl3_15 | ~spl3_18 | ~spl3_19)),
% 0.22/0.51    inference(forward_demodulation,[],[f331,f273])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl3_9 | ~spl3_15 | ~spl3_18)),
% 0.22/0.51    inference(forward_demodulation,[],[f330,f260])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl3_9 | ~spl3_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f220,f229])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_9),
% 0.22/0.51    inference(resolution,[],[f177,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f304,plain,(
% 0.22/0.51    spl3_21 | ~spl3_22 | ~spl3_11 | ~spl3_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f293,f202,f190,f301,f297])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    spl3_11 <=> v1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    spl3_13 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.51  fof(f293,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | k1_xboole_0 = sK2 | (~spl3_11 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f208,f191])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f190])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl3_13),
% 0.22/0.51    inference(superposition,[],[f83,f204])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    sK1 = k2_relat_1(sK2) | ~spl3_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f202])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    spl3_19 | ~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f269,f202,f190,f122,f117,f271])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f269,plain,(
% 0.22/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f214,f191])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.22/0.51    inference(forward_demodulation,[],[f138,f204])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f134,f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f124,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f122])).
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    spl3_18 | ~spl3_1 | ~spl3_2 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f256,f190,f122,f117,f258])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f139,f191])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f135,f119])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f124,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f44])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    ~spl3_1 | ~spl3_11 | spl3_15),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f236])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    $false | (~spl3_1 | ~spl3_11 | spl3_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f235,f191])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | (~spl3_1 | spl3_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f232,f119])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_15),
% 0.22/0.51    inference(resolution,[],[f230,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    ~v1_relat_1(k2_funct_1(sK2)) | spl3_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f228])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    ~spl3_4 | spl3_11),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f211])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    $false | (~spl3_4 | spl3_11)),
% 0.22/0.51    inference(resolution,[],[f194,f149])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_11),
% 0.22/0.51    inference(resolution,[],[f192,f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f190])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    spl3_13 | ~spl3_4 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f160,f152,f147,f202])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    spl3_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    sK1 = k2_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f158,f149])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_5),
% 0.22/0.51    inference(superposition,[],[f154,f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f152])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    ~spl3_11 | ~spl3_1 | spl3_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f188,f176,f117,f190])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | (~spl3_1 | spl3_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f129,f178])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    ~v1_funct_1(k2_funct_1(sK2)) | spl3_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f176])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.22/0.51    inference(resolution,[],[f119,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f64,f176,f172,f168])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    spl3_7 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    spl3_8 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f28])).
% 0.22/0.51  fof(f28,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f69,f152])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f67,f147])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f66,f141])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f68,f122])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    v2_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f65,f117])).
% 0.22/0.51  % (15738)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (15721)------------------------------
% 0.22/0.51  % (15721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15721)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (15721)Memory used [KB]: 11001
% 0.22/0.51  % (15721)Time elapsed: 0.083 s
% 0.22/0.51  % (15721)------------------------------
% 0.22/0.51  % (15721)------------------------------
% 0.22/0.52  % (15717)Success in time 0.154 s
%------------------------------------------------------------------------------
