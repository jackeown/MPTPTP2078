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
% DateTime   : Thu Dec  3 13:00:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 456 expanded)
%              Number of leaves         :   43 ( 166 expanded)
%              Depth                    :   16
%              Number of atoms          :  627 (1634 expanded)
%              Number of equality atoms :  147 ( 530 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f105,f114,f170,f238,f253,f358,f477,f520,f526,f538,f544,f659,f671,f677,f781,f798,f815,f834,f975,f1042,f1097,f1148,f1150,f1161,f1235,f1237,f1301,f1306])).

fof(f1306,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK1,sK1)
    | r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1301,plain,
    ( ~ spl4_6
    | ~ spl4_15
    | spl4_32
    | ~ spl4_69 ),
    inference(avatar_contradiction_clause,[],[f1300])).

fof(f1300,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_15
    | spl4_32
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f1279,f1299])).

fof(f1299,plain,
    ( ! [X6] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X6)
    | ~ spl4_6
    | spl4_32
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f495,f1298])).

fof(f1298,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl4_6
    | spl4_32
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f1271,f104])).

fof(f104,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1271,plain,
    ( sK0 != k1_relat_1(k1_xboole_0)
    | spl4_32
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f541,f1096])).

fof(f1096,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f1094])).

fof(f1094,plain,
    ( spl4_69
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f541,plain,
    ( sK0 != k1_relat_1(sK3)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl4_32
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f495,plain,(
    ! [X6] :
      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X6) ) ),
    inference(forward_demodulation,[],[f493,f482])).

fof(f482,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f117,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f117,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f493,plain,(
    ! [X6] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X6,k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X6) ) ),
    inference(resolution,[],[f117,f76])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f71,f66])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f71,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f1279,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f246,f104])).

fof(f246,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl4_15
  <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1237,plain,
    ( ~ spl4_6
    | spl4_7
    | ~ spl4_54
    | ~ spl4_67
    | ~ spl4_69 ),
    inference(avatar_contradiction_clause,[],[f1236])).

fof(f1236,plain,
    ( $false
    | ~ spl4_6
    | spl4_7
    | ~ spl4_54
    | ~ spl4_67
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f1024,f1225])).

fof(f1225,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_6
    | spl4_7
    | ~ spl4_54
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f1224,f1096])).

fof(f1224,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_6
    | spl4_7
    | ~ spl4_54
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f894,f1190])).

fof(f1190,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_6
    | spl4_7
    | ~ spl4_54
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f1189,f117])).

fof(f1189,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2
    | ~ spl4_6
    | spl4_7
    | ~ spl4_54
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f1188,f1096])).

fof(f1188,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2
    | ~ spl4_6
    | spl4_7
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f1187,f66])).

fof(f1187,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_xboole_0 = sK2
    | ~ spl4_6
    | spl4_7
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f1186,f104])).

fof(f1186,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_7
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f818,f109])).

fof(f109,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_7
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f818,plain,
    ( v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_54 ),
    inference(trivial_inequality_removal,[],[f817])).

fof(f817,plain,
    ( sK0 != sK0
    | v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_54 ),
    inference(superposition,[],[f59,f814])).

fof(f814,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f812])).

fof(f812,plain,
    ( spl4_54
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f894,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl4_6
    | spl4_7 ),
    inference(superposition,[],[f109,f104])).

fof(f1024,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f1022,plain,
    ( spl4_67
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f1235,plain,
    ( ~ spl4_6
    | spl4_7
    | ~ spl4_54
    | ~ spl4_69
    | spl4_74 ),
    inference(avatar_contradiction_clause,[],[f1234])).

fof(f1234,plain,
    ( $false
    | ~ spl4_6
    | spl4_7
    | ~ spl4_54
    | ~ spl4_69
    | spl4_74 ),
    inference(subsumption_resolution,[],[f1121,f1222])).

fof(f1222,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_6
    | spl4_7
    | ~ spl4_54
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f1221,f1190])).

fof(f1221,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_54
    | ~ spl4_69 ),
    inference(forward_demodulation,[],[f909,f1096])).

fof(f909,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ spl4_6
    | ~ spl4_54 ),
    inference(superposition,[],[f814,f104])).

fof(f1121,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_74 ),
    inference(avatar_component_clause,[],[f1120])).

fof(f1120,plain,
    ( spl4_74
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f1161,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK1,sK1)
    | k1_xboole_0 != sK1
    | v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1150,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != sK1
    | v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

% (31092)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f1148,plain,
    ( spl4_67
    | ~ spl4_74 ),
    inference(avatar_contradiction_clause,[],[f1147])).

fof(f1147,plain,
    ( $false
    | spl4_67
    | ~ spl4_74 ),
    inference(subsumption_resolution,[],[f1122,f1130])).

fof(f1130,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_67 ),
    inference(unit_resulting_resolution,[],[f117,f1023,f75])).

fof(f75,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f70,f66])).

fof(f70,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1023,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_67 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f1122,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f1120])).

fof(f1097,plain,
    ( spl4_69
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f1046,f668,f1094])).

fof(f668,plain,
    ( spl4_39
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f1046,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_39 ),
    inference(unit_resulting_resolution,[],[f41,f669,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f669,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f668])).

fof(f1042,plain,
    ( spl4_39
    | ~ spl4_53
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f856,f831,f795,f668])).

fof(f795,plain,
    ( spl4_53
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f831,plain,
    ( spl4_57
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f856,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_53
    | ~ spl4_57 ),
    inference(forward_demodulation,[],[f846,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f846,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_53
    | ~ spl4_57 ),
    inference(superposition,[],[f797,f833])).

fof(f833,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f831])).

fof(f797,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f795])).

fof(f975,plain,
    ( spl4_14
    | ~ spl4_32
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f887,f656,f540,f235])).

fof(f235,plain,
    ( spl4_14
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f656,plain,
    ( spl4_38
  <=> r1_tarski(k1_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f887,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_32
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f658,f542])).

fof(f542,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f540])).

fof(f658,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f656])).

fof(f834,plain,
    ( spl4_57
    | spl4_7
    | ~ spl4_8
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f816,f812,f111,f107,f831])).

fof(f111,plain,
    ( spl4_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f816,plain,
    ( k1_xboole_0 = sK2
    | spl4_7
    | ~ spl4_8
    | ~ spl4_54 ),
    inference(unit_resulting_resolution,[],[f109,f112,f814,f59])).

fof(f112,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f815,plain,
    ( spl4_54
    | ~ spl4_8
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f792,f540,f111,f812])).

fof(f792,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_8
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f782,f542])).

fof(f782,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f112,f55])).

fof(f798,plain,
    ( spl4_53
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f786,f111,f795])).

fof(f786,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f112,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f781,plain,
    ( spl4_8
    | ~ spl4_10
    | ~ spl4_32
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f690,f674,f540,f167,f111])).

fof(f167,plain,
    ( spl4_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f674,plain,
    ( spl4_40
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f690,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_10
    | ~ spl4_32
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f687,f542])).

fof(f687,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))
    | ~ spl4_10
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f169,f63,f676,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f676,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f674])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f169,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f167])).

fof(f677,plain,
    ( spl4_40
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f527,f523,f674])).

fof(f523,plain,
    ( spl4_29
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f527,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl4_29 ),
    inference(unit_resulting_resolution,[],[f525,f47])).

fof(f525,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f523])).

fof(f671,plain,
    ( ~ spl4_39
    | spl4_11 ),
    inference(avatar_split_clause,[],[f666,f199,f668])).

fof(f199,plain,
    ( spl4_11
  <=> v4_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f666,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl4_11 ),
    inference(forward_demodulation,[],[f660,f66])).

fof(f660,plain,
    ( ! [X0] : ~ r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X0))
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f200,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f56,f48])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f200,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f199])).

fof(f659,plain,
    ( spl4_38
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f431,f199,f167,f656])).

fof(f431,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f169,f201,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f201,plain,
    ( v4_relat_1(sK3,k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f199])).

fof(f544,plain,
    ( spl4_32
    | ~ spl4_22
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f543,f535,f338,f540])).

fof(f338,plain,
    ( spl4_22
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f535,plain,
    ( spl4_31
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f543,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_22
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f537,f340])).

fof(f340,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f338])).

fof(f537,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f535])).

fof(f538,plain,
    ( spl4_31
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f181,f88,f535])).

fof(f88,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f181,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f55,f90])).

fof(f90,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f526,plain,
    ( spl4_29
    | ~ spl4_3
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f521,f517,f88,f523])).

fof(f517,plain,
    ( spl4_28
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f521,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))
    | ~ spl4_3
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f519,f172])).

fof(f172,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f90])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f519,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK2))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f517])).

fof(f520,plain,
    ( spl4_28
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f119,f93,f517])).

fof(f93,plain,
    ( spl4_4
  <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f119,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK2))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f95,f48])).

fof(f95,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f477,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_3
    | spl4_5 ),
    inference(avatar_split_clause,[],[f390,f98,f88,f83,f338])).

fof(f83,plain,
    ( spl4_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f98,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f390,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f85,f90,f100,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,
    ( k1_xboole_0 != sK1
    | spl4_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f85,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f358,plain,
    ( ~ spl4_5
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl4_5
    | spl4_17 ),
    inference(subsumption_resolution,[],[f348,f66])).

fof(f348,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | spl4_17 ),
    inference(superposition,[],[f257,f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f257,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,sK1)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl4_17
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f253,plain,
    ( spl4_16
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f115,f88,f250])).

fof(f250,plain,
    ( spl4_16
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f115,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f90,f47])).

fof(f238,plain,
    ( ~ spl4_14
    | spl4_6 ),
    inference(avatar_split_clause,[],[f223,f102,f235])).

fof(f223,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f41,f103,f46])).

fof(f103,plain,
    ( k1_xboole_0 != sK0
    | spl4_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f170,plain,
    ( spl4_10
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f141,f88,f167])).

fof(f141,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f90,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f114,plain,
    ( ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f72,f111,f107])).

fof(f72,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(subsumption_resolution,[],[f40,f35])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

% (31088)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (31085)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f40,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f105,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f39,f102,f98])).

fof(f39,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f38,f93])).

fof(f38,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f86,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f83])).

fof(f36,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:29:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (31098)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.46  % (31090)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.47  % (31082)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (31077)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (31074)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (31078)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (31081)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (31081)Refutation not found, incomplete strategy% (31081)------------------------------
% 0.20/0.51  % (31081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31081)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (31081)Memory used [KB]: 10618
% 0.20/0.51  % (31081)Time elapsed: 0.101 s
% 0.20/0.51  % (31081)------------------------------
% 0.20/0.51  % (31081)------------------------------
% 0.20/0.52  % (31096)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (31093)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (31095)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (31094)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (31087)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (31076)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (31079)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (31098)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f1307,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f86,f91,f96,f105,f114,f170,f238,f253,f358,f477,f520,f526,f538,f544,f659,f671,f677,f781,f798,f815,f834,f975,f1042,f1097,f1148,f1150,f1161,f1235,f1237,f1301,f1306])).
% 0.20/0.53  fof(f1306,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK1,sK1) | r1_tarski(sK3,k1_xboole_0) | ~r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f1301,plain,(
% 0.20/0.53    ~spl4_6 | ~spl4_15 | spl4_32 | ~spl4_69),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1300])).
% 0.20/0.53  fof(f1300,plain,(
% 0.20/0.53    $false | (~spl4_6 | ~spl4_15 | spl4_32 | ~spl4_69)),
% 0.20/0.53    inference(subsumption_resolution,[],[f1279,f1299])).
% 0.20/0.53  fof(f1299,plain,(
% 0.20/0.53    ( ! [X6] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X6)) ) | (~spl4_6 | spl4_32 | ~spl4_69)),
% 0.20/0.53    inference(subsumption_resolution,[],[f495,f1298])).
% 0.20/0.53  fof(f1298,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl4_6 | spl4_32 | ~spl4_69)),
% 0.20/0.53    inference(forward_demodulation,[],[f1271,f104])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~spl4_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f102])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    spl4_6 <=> k1_xboole_0 = sK0),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.53  fof(f1271,plain,(
% 0.20/0.53    sK0 != k1_relat_1(k1_xboole_0) | (spl4_32 | ~spl4_69)),
% 0.20/0.53    inference(forward_demodulation,[],[f541,f1096])).
% 0.20/0.53  fof(f1096,plain,(
% 0.20/0.53    k1_xboole_0 = sK3 | ~spl4_69),
% 0.20/0.53    inference(avatar_component_clause,[],[f1094])).
% 0.20/0.53  fof(f1094,plain,(
% 0.20/0.53    spl4_69 <=> k1_xboole_0 = sK3),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.20/0.53  fof(f541,plain,(
% 0.20/0.53    sK0 != k1_relat_1(sK3) | spl4_32),
% 0.20/0.53    inference(avatar_component_clause,[],[f540])).
% 0.20/0.53  fof(f540,plain,(
% 0.20/0.53    spl4_32 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.53  fof(f495,plain,(
% 0.20/0.53    ( ! [X6] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X6)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f493,f482])).
% 0.20/0.53  fof(f482,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f117,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f41,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.53  fof(f493,plain,(
% 0.20/0.53    ( ! [X6] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X6,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X6)) )),
% 0.20/0.53    inference(resolution,[],[f117,f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f71,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f1279,plain,(
% 0.20/0.53    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_6 | ~spl4_15)),
% 0.20/0.53    inference(forward_demodulation,[],[f246,f104])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~spl4_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f244])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    spl4_15 <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.53  fof(f1237,plain,(
% 0.20/0.53    ~spl4_6 | spl4_7 | ~spl4_54 | ~spl4_67 | ~spl4_69),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1236])).
% 0.20/0.53  fof(f1236,plain,(
% 0.20/0.53    $false | (~spl4_6 | spl4_7 | ~spl4_54 | ~spl4_67 | ~spl4_69)),
% 0.20/0.53    inference(subsumption_resolution,[],[f1024,f1225])).
% 0.20/0.53  fof(f1225,plain,(
% 0.20/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_6 | spl4_7 | ~spl4_54 | ~spl4_69)),
% 0.20/0.53    inference(forward_demodulation,[],[f1224,f1096])).
% 0.20/0.53  fof(f1224,plain,(
% 0.20/0.53    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_6 | spl4_7 | ~spl4_54 | ~spl4_69)),
% 0.20/0.53    inference(forward_demodulation,[],[f894,f1190])).
% 0.20/0.53  fof(f1190,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | (~spl4_6 | spl4_7 | ~spl4_54 | ~spl4_69)),
% 0.20/0.53    inference(subsumption_resolution,[],[f1189,f117])).
% 0.20/0.53  fof(f1189,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2 | (~spl4_6 | spl4_7 | ~spl4_54 | ~spl4_69)),
% 0.20/0.53    inference(forward_demodulation,[],[f1188,f1096])).
% 0.20/0.53  fof(f1188,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2 | (~spl4_6 | spl4_7 | ~spl4_54)),
% 0.20/0.53    inference(forward_demodulation,[],[f1187,f66])).
% 0.20/0.53  fof(f1187,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | k1_xboole_0 = sK2 | (~spl4_6 | spl4_7 | ~spl4_54)),
% 0.20/0.53    inference(forward_demodulation,[],[f1186,f104])).
% 0.20/0.53  fof(f1186,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (spl4_7 | ~spl4_54)),
% 0.20/0.53    inference(subsumption_resolution,[],[f818,f109])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ~v1_funct_2(sK3,sK0,sK2) | spl4_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl4_7 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.53  fof(f818,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl4_54),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f817])).
% 0.20/0.53  fof(f817,plain,(
% 0.20/0.53    sK0 != sK0 | v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl4_54),
% 0.20/0.53    inference(superposition,[],[f59,f814])).
% 0.20/0.53  fof(f814,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK2,sK3) | ~spl4_54),
% 0.20/0.53    inference(avatar_component_clause,[],[f812])).
% 0.20/0.53  fof(f812,plain,(
% 0.20/0.53    spl4_54 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f894,plain,(
% 0.20/0.53    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl4_6 | spl4_7)),
% 0.20/0.53    inference(superposition,[],[f109,f104])).
% 0.20/0.53  fof(f1024,plain,(
% 0.20/0.53    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl4_67),
% 0.20/0.53    inference(avatar_component_clause,[],[f1022])).
% 0.20/0.53  fof(f1022,plain,(
% 0.20/0.53    spl4_67 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.20/0.53  fof(f1235,plain,(
% 0.20/0.53    ~spl4_6 | spl4_7 | ~spl4_54 | ~spl4_69 | spl4_74),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1234])).
% 0.20/0.53  fof(f1234,plain,(
% 0.20/0.53    $false | (~spl4_6 | spl4_7 | ~spl4_54 | ~spl4_69 | spl4_74)),
% 0.20/0.53    inference(subsumption_resolution,[],[f1121,f1222])).
% 0.20/0.53  fof(f1222,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_6 | spl4_7 | ~spl4_54 | ~spl4_69)),
% 0.20/0.53    inference(forward_demodulation,[],[f1221,f1190])).
% 0.20/0.53  fof(f1221,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | (~spl4_6 | ~spl4_54 | ~spl4_69)),
% 0.20/0.53    inference(forward_demodulation,[],[f909,f1096])).
% 0.20/0.53  fof(f909,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3) | (~spl4_6 | ~spl4_54)),
% 0.20/0.53    inference(superposition,[],[f814,f104])).
% 0.20/0.53  fof(f1121,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl4_74),
% 0.20/0.53    inference(avatar_component_clause,[],[f1120])).
% 0.20/0.53  fof(f1120,plain,(
% 0.20/0.53    spl4_74 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 0.20/0.53  fof(f1161,plain,(
% 0.20/0.53    k1_xboole_0 != sK3 | k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK1,sK1) | k1_xboole_0 != sK1 | v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | ~v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f1150,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | k1_xboole_0 != sK1 | v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  % (31092)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  fof(f1148,plain,(
% 0.20/0.53    spl4_67 | ~spl4_74),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1147])).
% 0.20/0.53  fof(f1147,plain,(
% 0.20/0.53    $false | (spl4_67 | ~spl4_74)),
% 0.20/0.53    inference(subsumption_resolution,[],[f1122,f1130])).
% 0.20/0.53  fof(f1130,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl4_67),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f117,f1023,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f70,f66])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.53    inference(equality_resolution,[],[f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f1023,plain,(
% 0.20/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl4_67),
% 0.20/0.53    inference(avatar_component_clause,[],[f1022])).
% 0.20/0.53  fof(f1122,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl4_74),
% 0.20/0.53    inference(avatar_component_clause,[],[f1120])).
% 0.20/0.53  fof(f1097,plain,(
% 0.20/0.53    spl4_69 | ~spl4_39),
% 0.20/0.53    inference(avatar_split_clause,[],[f1046,f668,f1094])).
% 0.20/0.53  fof(f668,plain,(
% 0.20/0.53    spl4_39 <=> r1_tarski(sK3,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.53  fof(f1046,plain,(
% 0.20/0.53    k1_xboole_0 = sK3 | ~spl4_39),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f41,f669,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f669,plain,(
% 0.20/0.53    r1_tarski(sK3,k1_xboole_0) | ~spl4_39),
% 0.20/0.53    inference(avatar_component_clause,[],[f668])).
% 0.20/0.53  fof(f1042,plain,(
% 0.20/0.53    spl4_39 | ~spl4_53 | ~spl4_57),
% 0.20/0.53    inference(avatar_split_clause,[],[f856,f831,f795,f668])).
% 0.20/0.53  fof(f795,plain,(
% 0.20/0.53    spl4_53 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.20/0.53  fof(f831,plain,(
% 0.20/0.53    spl4_57 <=> k1_xboole_0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.20/0.53  fof(f856,plain,(
% 0.20/0.53    r1_tarski(sK3,k1_xboole_0) | (~spl4_53 | ~spl4_57)),
% 0.20/0.53    inference(forward_demodulation,[],[f846,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f846,plain,(
% 0.20/0.53    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl4_53 | ~spl4_57)),
% 0.20/0.53    inference(superposition,[],[f797,f833])).
% 0.20/0.53  fof(f833,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | ~spl4_57),
% 0.20/0.53    inference(avatar_component_clause,[],[f831])).
% 0.20/0.53  fof(f797,plain,(
% 0.20/0.53    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | ~spl4_53),
% 0.20/0.53    inference(avatar_component_clause,[],[f795])).
% 0.20/0.53  fof(f975,plain,(
% 0.20/0.53    spl4_14 | ~spl4_32 | ~spl4_38),
% 0.20/0.53    inference(avatar_split_clause,[],[f887,f656,f540,f235])).
% 0.20/0.53  fof(f235,plain,(
% 0.20/0.53    spl4_14 <=> r1_tarski(sK0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.53  fof(f656,plain,(
% 0.20/0.53    spl4_38 <=> r1_tarski(k1_relat_1(sK3),k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.53  fof(f887,plain,(
% 0.20/0.53    r1_tarski(sK0,k1_xboole_0) | (~spl4_32 | ~spl4_38)),
% 0.20/0.53    inference(forward_demodulation,[],[f658,f542])).
% 0.20/0.53  fof(f542,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK3) | ~spl4_32),
% 0.20/0.53    inference(avatar_component_clause,[],[f540])).
% 0.20/0.53  fof(f658,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK3),k1_xboole_0) | ~spl4_38),
% 0.20/0.53    inference(avatar_component_clause,[],[f656])).
% 0.20/0.53  fof(f834,plain,(
% 0.20/0.53    spl4_57 | spl4_7 | ~spl4_8 | ~spl4_54),
% 0.20/0.53    inference(avatar_split_clause,[],[f816,f812,f111,f107,f831])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    spl4_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.53  fof(f816,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | (spl4_7 | ~spl4_8 | ~spl4_54)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f109,f112,f814,f59])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl4_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f111])).
% 0.20/0.53  fof(f815,plain,(
% 0.20/0.53    spl4_54 | ~spl4_8 | ~spl4_32),
% 0.20/0.53    inference(avatar_split_clause,[],[f792,f540,f111,f812])).
% 0.20/0.53  fof(f792,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK2,sK3) | (~spl4_8 | ~spl4_32)),
% 0.20/0.53    inference(forward_demodulation,[],[f782,f542])).
% 0.20/0.53  fof(f782,plain,(
% 0.20/0.53    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl4_8),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f112,f55])).
% 0.20/0.53  fof(f798,plain,(
% 0.20/0.53    spl4_53 | ~spl4_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f786,f111,f795])).
% 0.20/0.53  fof(f786,plain,(
% 0.20/0.53    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | ~spl4_8),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f112,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f781,plain,(
% 0.20/0.53    spl4_8 | ~spl4_10 | ~spl4_32 | ~spl4_40),
% 0.20/0.53    inference(avatar_split_clause,[],[f690,f674,f540,f167,f111])).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    spl4_10 <=> v1_relat_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.53  fof(f674,plain,(
% 0.20/0.53    spl4_40 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.20/0.53  fof(f690,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl4_10 | ~spl4_32 | ~spl4_40)),
% 0.20/0.53    inference(forward_demodulation,[],[f687,f542])).
% 0.20/0.53  fof(f687,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) | (~spl4_10 | ~spl4_40)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f169,f63,f676,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.53  fof(f676,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK3),sK2) | ~spl4_40),
% 0.20/0.53    inference(avatar_component_clause,[],[f674])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~spl4_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f167])).
% 0.20/0.53  fof(f677,plain,(
% 0.20/0.53    spl4_40 | ~spl4_29),
% 0.20/0.53    inference(avatar_split_clause,[],[f527,f523,f674])).
% 0.20/0.53  fof(f523,plain,(
% 0.20/0.53    spl4_29 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.20/0.53  fof(f527,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK3),sK2) | ~spl4_29),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f525,f47])).
% 0.20/0.53  fof(f525,plain,(
% 0.20/0.53    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | ~spl4_29),
% 0.20/0.53    inference(avatar_component_clause,[],[f523])).
% 0.20/0.53  fof(f671,plain,(
% 0.20/0.53    ~spl4_39 | spl4_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f666,f199,f668])).
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    spl4_11 <=> v4_relat_1(sK3,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.53  fof(f666,plain,(
% 0.20/0.53    ~r1_tarski(sK3,k1_xboole_0) | spl4_11),
% 0.20/0.53    inference(forward_demodulation,[],[f660,f66])).
% 0.20/0.53  fof(f660,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X0))) ) | spl4_11),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f200,f159])).
% 0.20/0.53  fof(f159,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v4_relat_1(X0,X1)) )),
% 0.20/0.53    inference(resolution,[],[f56,f48])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    ~v4_relat_1(sK3,k1_xboole_0) | spl4_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f199])).
% 0.20/0.53  fof(f659,plain,(
% 0.20/0.53    spl4_38 | ~spl4_10 | ~spl4_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f431,f199,f167,f656])).
% 0.20/0.53  fof(f431,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK3),k1_xboole_0) | (~spl4_10 | ~spl4_11)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f169,f201,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    v4_relat_1(sK3,k1_xboole_0) | ~spl4_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f199])).
% 0.20/0.53  fof(f544,plain,(
% 0.20/0.53    spl4_32 | ~spl4_22 | ~spl4_31),
% 0.20/0.53    inference(avatar_split_clause,[],[f543,f535,f338,f540])).
% 0.20/0.53  fof(f338,plain,(
% 0.20/0.53    spl4_22 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.53  fof(f535,plain,(
% 0.20/0.53    spl4_31 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.20/0.53  fof(f543,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK3) | (~spl4_22 | ~spl4_31)),
% 0.20/0.53    inference(forward_demodulation,[],[f537,f340])).
% 0.20/0.53  fof(f340,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_22),
% 0.20/0.53    inference(avatar_component_clause,[],[f338])).
% 0.20/0.53  fof(f537,plain,(
% 0.20/0.53    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_31),
% 0.20/0.53    inference(avatar_component_clause,[],[f535])).
% 0.20/0.53  fof(f538,plain,(
% 0.20/0.53    spl4_31 | ~spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f181,f88,f535])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_3),
% 0.20/0.53    inference(resolution,[],[f55,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f88])).
% 0.20/0.53  fof(f526,plain,(
% 0.20/0.53    spl4_29 | ~spl4_3 | ~spl4_28),
% 0.20/0.53    inference(avatar_split_clause,[],[f521,f517,f88,f523])).
% 0.20/0.53  fof(f517,plain,(
% 0.20/0.53    spl4_28 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.53  fof(f521,plain,(
% 0.20/0.53    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) | (~spl4_3 | ~spl4_28)),
% 0.20/0.53    inference(forward_demodulation,[],[f519,f172])).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl4_3),
% 0.20/0.53    inference(resolution,[],[f54,f90])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.53  fof(f519,plain,(
% 0.20/0.53    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK2)) | ~spl4_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f517])).
% 0.20/0.53  fof(f520,plain,(
% 0.20/0.53    spl4_28 | ~spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f119,f93,f517])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    spl4_4 <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK2)) | ~spl4_4),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f95,f48])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) | ~spl4_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f93])).
% 0.20/0.53  fof(f477,plain,(
% 0.20/0.53    spl4_22 | ~spl4_2 | ~spl4_3 | spl4_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f390,f98,f88,f83,f338])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    spl4_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    spl4_5 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.53  fof(f390,plain,(
% 0.20/0.53    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_2 | ~spl4_3 | spl4_5)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f85,f90,f100,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | spl4_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f98])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK1) | ~spl4_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f83])).
% 0.20/0.53  fof(f358,plain,(
% 0.20/0.53    ~spl4_5 | spl4_17),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f357])).
% 0.20/0.53  fof(f357,plain,(
% 0.20/0.53    $false | (~spl4_5 | spl4_17)),
% 0.20/0.53    inference(subsumption_resolution,[],[f348,f66])).
% 0.20/0.53  fof(f348,plain,(
% 0.20/0.53    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (~spl4_5 | spl4_17)),
% 0.20/0.53    inference(superposition,[],[f257,f99])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    k1_xboole_0 = sK1 | ~spl4_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f98])).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    k1_xboole_0 != k2_zfmisc_1(sK1,sK1) | spl4_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f255])).
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    spl4_17 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.53  fof(f253,plain,(
% 0.20/0.53    spl4_16 | ~spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f115,f88,f250])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    spl4_16 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_3),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f90,f47])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    ~spl4_14 | spl4_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f223,f102,f235])).
% 0.20/0.53  fof(f223,plain,(
% 0.20/0.53    ~r1_tarski(sK0,k1_xboole_0) | spl4_6),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f41,f103,f46])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | spl4_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f102])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    spl4_10 | ~spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f141,f88,f167])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~spl4_3),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f90,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ~spl4_7 | ~spl4_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f72,f111,f107])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f40,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f12])).
% 0.20/0.53  % (31088)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (31085)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  fof(f12,conjecture,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    ~spl4_5 | spl4_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f39,f102,f98])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    spl4_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f38,f93])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f37,f88])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    spl4_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f36,f83])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (31098)------------------------------
% 0.20/0.53  % (31098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31098)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (31098)Memory used [KB]: 11385
% 0.20/0.53  % (31098)Time elapsed: 0.119 s
% 0.20/0.53  % (31098)------------------------------
% 0.20/0.53  % (31098)------------------------------
% 0.20/0.53  % (31084)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.48/0.54  % (31073)Success in time 0.186 s
%------------------------------------------------------------------------------
