%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:40 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 359 expanded)
%              Number of leaves         :   39 ( 131 expanded)
%              Depth                    :   13
%              Number of atoms          :  522 (1271 expanded)
%              Number of equality atoms :  134 ( 440 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f883,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f105,f117,f122,f131,f147,f157,f205,f231,f280,f310,f324,f368,f446,f448,f526,f592,f613,f638,f674,f690,f707,f712,f726,f728,f882])).

fof(f882,plain,
    ( spl6_14
    | ~ spl6_15
    | ~ spl6_42
    | spl6_44
    | ~ spl6_48 ),
    inference(avatar_contradiction_clause,[],[f881])).

fof(f881,plain,
    ( $false
    | spl6_14
    | ~ spl6_15
    | ~ spl6_42
    | spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f880,f564])).

fof(f564,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | spl6_44 ),
    inference(avatar_component_clause,[],[f562])).

fof(f562,plain,
    ( spl6_44
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f880,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | spl6_14
    | ~ spl6_15
    | ~ spl6_42
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f866,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f866,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | spl6_14
    | ~ spl6_15
    | ~ spl6_42
    | ~ spl6_48 ),
    inference(backward_demodulation,[],[f525,f856])).

fof(f856,plain,
    ( k1_xboole_0 = sK2
    | spl6_14
    | ~ spl6_15
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f855,f203])).

fof(f203,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl6_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f855,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_14
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f854,f200])).

fof(f200,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl6_14
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f854,plain,
    ( v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_48 ),
    inference(trivial_inequality_removal,[],[f853])).

fof(f853,plain,
    ( sK0 != sK0
    | v1_funct_2(sK3,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_48 ),
    inference(superposition,[],[f75,f612])).

fof(f612,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f610])).

fof(f610,plain,
    ( spl6_48
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f525,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f523])).

% (32280)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (32295)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (32300)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (32299)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (32292)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f523,plain,
    ( spl6_42
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f728,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | sK0 != k1_relat_1(sK3)
    | v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_2(sK3,k1_xboole_0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f726,plain,
    ( ~ spl6_17
    | ~ spl6_46
    | spl6_57 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | ~ spl6_17
    | ~ spl6_46
    | spl6_57 ),
    inference(unit_resulting_resolution,[],[f224,f591,f711,f252])).

fof(f252,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f87,f83])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f711,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | spl6_57 ),
    inference(avatar_component_clause,[],[f709])).

fof(f709,plain,
    ( spl6_57
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f591,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl6_46
  <=> ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f224,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl6_17
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f712,plain,
    ( ~ spl6_57
    | spl6_40
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f679,f562,f491,f709])).

fof(f491,plain,
    ( spl6_40
  <=> v1_funct_2(sK3,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f679,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | spl6_40
    | ~ spl6_44 ),
    inference(backward_demodulation,[],[f493,f642])).

fof(f642,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_44 ),
    inference(resolution,[],[f563,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f563,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f562])).

fof(f493,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl6_40 ),
    inference(avatar_component_clause,[],[f491])).

fof(f707,plain,
    ( spl6_54
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f644,f562,f685])).

fof(f685,plain,
    ( spl6_54
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f644,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f643,f142])).

fof(f142,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f134,f136])).

fof(f136,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f133,f83])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) ),
    inference(resolution,[],[f57,f54])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f134,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(superposition,[],[f57,f82])).

fof(f643,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3
    | ~ spl6_44 ),
    inference(resolution,[],[f563,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f690,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f674,plain,
    ( ~ spl6_53
    | ~ spl6_8
    | spl6_28 ),
    inference(avatar_split_clause,[],[f665,f321,f128,f671])).

fof(f671,plain,
    ( spl6_53
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f128,plain,
    ( spl6_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f321,plain,
    ( spl6_28
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f665,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ spl6_8
    | spl6_28 ),
    inference(forward_demodulation,[],[f322,f130])).

fof(f130,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f322,plain,
    ( sK0 != k1_relat_1(sK3)
    | spl6_28 ),
    inference(avatar_component_clause,[],[f321])).

fof(f638,plain,
    ( spl6_44
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f622,f154,f124,f562])).

fof(f124,plain,
    ( spl6_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f154,plain,
    ( spl6_10
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f622,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f618,f82])).

fof(f618,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f156,f125])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f156,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f613,plain,
    ( spl6_48
    | ~ spl6_15
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f604,f321,f202,f610])).

fof(f604,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl6_15
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f567,f323])).

fof(f323,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f321])).

fof(f567,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl6_15 ),
    inference(resolution,[],[f203,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f592,plain,
    ( spl6_46
    | ~ spl6_9
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f430,f223,f144,f590])).

fof(f144,plain,
    ( spl6_9
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f430,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl6_9
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f428,f146])).

fof(f146,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f428,plain,
    ( ! [X0] : k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl6_17 ),
    inference(resolution,[],[f216,f224])).

fof(f216,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relat_1(X3) = k1_relset_1(k1_xboole_0,X2,X3) ) ),
    inference(superposition,[],[f70,f83])).

fof(f526,plain,
    ( spl6_42
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f515,f202,f523])).

fof(f515,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ spl6_15 ),
    inference(resolution,[],[f203,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f448,plain,
    ( spl6_15
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f447,f444,f202])).

fof(f444,plain,
    ( spl6_37
  <=> ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f447,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_37 ),
    inference(resolution,[],[f445,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f445,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f444])).

fof(f446,plain,
    ( spl6_37
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f442,f365,f321,f307,f444])).

fof(f307,plain,
    ( spl6_26
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f365,plain,
    ( spl6_34
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | ~ spl6_26
    | ~ spl6_28
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f441,f323])).

fof(f441,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ r1_tarski(k1_relat_1(sK3),X0) )
    | ~ spl6_26
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f312,f367])).

fof(f367,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f365])).

fof(f312,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ r1_tarski(k1_relat_1(sK3),X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_26 ),
    inference(resolution,[],[f309,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f309,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f307])).

fof(f368,plain,
    ( spl6_34
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f359,f114,f365])).

fof(f114,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f359,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f150,f116])).

fof(f116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f53,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f324,plain,
    ( spl6_28
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f318,f277,f114,f321])).

fof(f277,plain,
    ( spl6_22
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f318,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f212,f279])).

fof(f279,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f277])).

fof(f212,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f70,f116])).

fof(f310,plain,
    ( spl6_26
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f295,f119,f114,f307])).

fof(f119,plain,
    ( spl6_6
  <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f295,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f121,f206])).

fof(f206,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f69,f116])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f121,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f280,plain,
    ( spl6_22
    | ~ spl6_3
    | ~ spl6_5
    | spl6_7 ),
    inference(avatar_split_clause,[],[f275,f124,f114,f102,f277])).

fof(f102,plain,
    ( spl6_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f275,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_3
    | ~ spl6_5
    | spl6_7 ),
    inference(subsumption_resolution,[],[f274,f116])).

fof(f274,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3
    | spl6_7 ),
    inference(subsumption_resolution,[],[f272,f126])).

fof(f126,plain,
    ( k1_xboole_0 != sK1
    | spl6_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f272,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(resolution,[],[f73,f104])).

fof(f104,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f231,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | spl6_17 ),
    inference(subsumption_resolution,[],[f228,f142])).

fof(f228,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_17 ),
    inference(resolution,[],[f225,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f225,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f223])).

fof(f205,plain,
    ( ~ spl6_14
    | ~ spl6_15
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f196,f92,f202,f198])).

fof(f92,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f196,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f50,f94])).

fof(f94,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f50,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f34])).

fof(f34,plain,
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

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f157,plain,
    ( spl6_10
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f140,f114,f154])).

fof(f140,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f63,f116])).

fof(f147,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f136,f144])).

fof(f131,plain,
    ( ~ spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f49,f128,f124])).

fof(f49,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f122,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f48,f119])).

fof(f48,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f117,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f47,f114])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f105,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f46,f102])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:59:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.46  % (32287)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.47  % (32297)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (32293)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.49  % (32289)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (32278)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (32277)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (32281)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (32284)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (32294)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (32282)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (32298)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (32290)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (32288)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (32296)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (32286)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (32285)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (32281)Refutation not found, incomplete strategy% (32281)------------------------------
% 0.20/0.52  % (32281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32281)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32281)Memory used [KB]: 10618
% 0.20/0.52  % (32281)Time elapsed: 0.040 s
% 0.20/0.52  % (32281)------------------------------
% 0.20/0.52  % (32281)------------------------------
% 1.38/0.53  % (32275)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.38/0.53  % (32279)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.38/0.54  % (32283)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.38/0.54  % (32276)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.54  % (32276)Refutation not found, incomplete strategy% (32276)------------------------------
% 1.38/0.54  % (32276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (32276)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (32276)Memory used [KB]: 10618
% 1.38/0.54  % (32276)Time elapsed: 0.129 s
% 1.38/0.54  % (32276)------------------------------
% 1.38/0.54  % (32276)------------------------------
% 1.54/0.54  % (32291)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.54/0.54  % (32277)Refutation found. Thanks to Tanya!
% 1.54/0.54  % SZS status Theorem for theBenchmark
% 1.54/0.54  % SZS output start Proof for theBenchmark
% 1.54/0.54  fof(f883,plain,(
% 1.54/0.54    $false),
% 1.54/0.54    inference(avatar_sat_refutation,[],[f95,f105,f117,f122,f131,f147,f157,f205,f231,f280,f310,f324,f368,f446,f448,f526,f592,f613,f638,f674,f690,f707,f712,f726,f728,f882])).
% 1.54/0.54  fof(f882,plain,(
% 1.54/0.54    spl6_14 | ~spl6_15 | ~spl6_42 | spl6_44 | ~spl6_48),
% 1.54/0.54    inference(avatar_contradiction_clause,[],[f881])).
% 1.54/0.54  fof(f881,plain,(
% 1.54/0.54    $false | (spl6_14 | ~spl6_15 | ~spl6_42 | spl6_44 | ~spl6_48)),
% 1.54/0.54    inference(subsumption_resolution,[],[f880,f564])).
% 1.54/0.54  fof(f564,plain,(
% 1.54/0.54    ~r1_tarski(sK3,k1_xboole_0) | spl6_44),
% 1.54/0.54    inference(avatar_component_clause,[],[f562])).
% 1.54/0.54  fof(f562,plain,(
% 1.54/0.54    spl6_44 <=> r1_tarski(sK3,k1_xboole_0)),
% 1.54/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 1.54/0.54  fof(f880,plain,(
% 1.54/0.54    r1_tarski(sK3,k1_xboole_0) | (spl6_14 | ~spl6_15 | ~spl6_42 | ~spl6_48)),
% 1.54/0.54    inference(forward_demodulation,[],[f866,f82])).
% 1.54/0.54  fof(f82,plain,(
% 1.54/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.54/0.54    inference(equality_resolution,[],[f67])).
% 1.54/0.54  fof(f67,plain,(
% 1.54/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.54/0.54    inference(cnf_transformation,[],[f43])).
% 1.54/0.54  fof(f43,plain,(
% 1.54/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.54/0.54    inference(flattening,[],[f42])).
% 1.54/0.54  fof(f42,plain,(
% 1.54/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.54/0.54    inference(nnf_transformation,[],[f5])).
% 1.54/0.54  fof(f5,axiom,(
% 1.54/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.54/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.54/0.54  fof(f866,plain,(
% 1.54/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (spl6_14 | ~spl6_15 | ~spl6_42 | ~spl6_48)),
% 1.54/0.54    inference(backward_demodulation,[],[f525,f856])).
% 1.54/0.54  fof(f856,plain,(
% 1.54/0.54    k1_xboole_0 = sK2 | (spl6_14 | ~spl6_15 | ~spl6_48)),
% 1.54/0.54    inference(subsumption_resolution,[],[f855,f203])).
% 1.54/0.54  fof(f203,plain,(
% 1.54/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_15),
% 1.54/0.54    inference(avatar_component_clause,[],[f202])).
% 1.54/0.54  fof(f202,plain,(
% 1.54/0.54    spl6_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.54/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.54/0.54  fof(f855,plain,(
% 1.54/0.54    k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (spl6_14 | ~spl6_48)),
% 1.54/0.54    inference(subsumption_resolution,[],[f854,f200])).
% 1.54/0.54  fof(f200,plain,(
% 1.54/0.54    ~v1_funct_2(sK3,sK0,sK2) | spl6_14),
% 1.54/0.54    inference(avatar_component_clause,[],[f198])).
% 1.54/0.54  fof(f198,plain,(
% 1.54/0.54    spl6_14 <=> v1_funct_2(sK3,sK0,sK2)),
% 1.54/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.54/0.54  fof(f854,plain,(
% 1.54/0.54    v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_48),
% 1.54/0.54    inference(trivial_inequality_removal,[],[f853])).
% 1.54/0.54  fof(f853,plain,(
% 1.54/0.54    sK0 != sK0 | v1_funct_2(sK3,sK0,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_48),
% 1.54/0.54    inference(superposition,[],[f75,f612])).
% 1.54/0.54  fof(f612,plain,(
% 1.54/0.54    sK0 = k1_relset_1(sK0,sK2,sK3) | ~spl6_48),
% 1.54/0.54    inference(avatar_component_clause,[],[f610])).
% 1.54/0.54  fof(f610,plain,(
% 1.54/0.54    spl6_48 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 1.54/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 1.54/0.54  fof(f75,plain,(
% 1.54/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.54    inference(cnf_transformation,[],[f44])).
% 1.54/0.54  fof(f44,plain,(
% 1.54/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.54    inference(nnf_transformation,[],[f32])).
% 1.54/0.54  fof(f32,plain,(
% 1.54/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.54    inference(flattening,[],[f31])).
% 1.54/0.54  fof(f31,plain,(
% 1.54/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.54    inference(ennf_transformation,[],[f17])).
% 1.54/0.54  fof(f17,axiom,(
% 1.54/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.54/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.54/0.54  fof(f525,plain,(
% 1.54/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | ~spl6_42),
% 1.54/0.54    inference(avatar_component_clause,[],[f523])).
% 1.54/0.55  % (32280)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.54/0.55  % (32295)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.54/0.55  % (32300)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.54/0.55  % (32299)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.54/0.56  % (32292)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.54/0.57  fof(f523,plain,(
% 1.54/0.57    spl6_42 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 1.54/0.57  fof(f728,plain,(
% 1.54/0.57    k1_xboole_0 != sK3 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | sK0 != k1_relat_1(sK3) | v1_funct_2(sK3,sK0,sK2) | ~v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.54/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.57  fof(f726,plain,(
% 1.54/0.57    ~spl6_17 | ~spl6_46 | spl6_57),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f725])).
% 1.54/0.57  fof(f725,plain,(
% 1.54/0.57    $false | (~spl6_17 | ~spl6_46 | spl6_57)),
% 1.54/0.57    inference(unit_resulting_resolution,[],[f224,f591,f711,f252])).
% 1.54/0.57  fof(f252,plain,(
% 1.54/0.57    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 1.54/0.57    inference(forward_demodulation,[],[f87,f83])).
% 1.54/0.57  fof(f83,plain,(
% 1.54/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.54/0.57    inference(equality_resolution,[],[f66])).
% 1.54/0.57  fof(f66,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f43])).
% 1.54/0.57  fof(f87,plain,(
% 1.54/0.57    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.54/0.57    inference(equality_resolution,[],[f76])).
% 1.54/0.57  fof(f76,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f44])).
% 1.54/0.57  fof(f711,plain,(
% 1.54/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | spl6_57),
% 1.54/0.57    inference(avatar_component_clause,[],[f709])).
% 1.54/0.57  fof(f709,plain,(
% 1.54/0.57    spl6_57 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 1.54/0.57  fof(f591,plain,(
% 1.54/0.57    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ) | ~spl6_46),
% 1.54/0.57    inference(avatar_component_clause,[],[f590])).
% 1.54/0.57  fof(f590,plain,(
% 1.54/0.57    spl6_46 <=> ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 1.54/0.57  fof(f224,plain,(
% 1.54/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl6_17),
% 1.54/0.57    inference(avatar_component_clause,[],[f223])).
% 1.54/0.57  fof(f223,plain,(
% 1.54/0.57    spl6_17 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.54/0.57  fof(f712,plain,(
% 1.54/0.57    ~spl6_57 | spl6_40 | ~spl6_44),
% 1.54/0.57    inference(avatar_split_clause,[],[f679,f562,f491,f709])).
% 1.54/0.57  fof(f491,plain,(
% 1.54/0.57    spl6_40 <=> v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.54/0.57  fof(f679,plain,(
% 1.54/0.57    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (spl6_40 | ~spl6_44)),
% 1.54/0.57    inference(backward_demodulation,[],[f493,f642])).
% 1.54/0.57  fof(f642,plain,(
% 1.54/0.57    k1_xboole_0 = sK3 | ~spl6_44),
% 1.54/0.57    inference(resolution,[],[f563,f54])).
% 1.54/0.57  fof(f54,plain,(
% 1.54/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f23])).
% 1.54/0.57  fof(f23,plain,(
% 1.54/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.54/0.57    inference(ennf_transformation,[],[f4])).
% 1.54/0.57  fof(f4,axiom,(
% 1.54/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.54/0.57  fof(f563,plain,(
% 1.54/0.57    r1_tarski(sK3,k1_xboole_0) | ~spl6_44),
% 1.54/0.57    inference(avatar_component_clause,[],[f562])).
% 1.54/0.57  fof(f493,plain,(
% 1.54/0.57    ~v1_funct_2(sK3,k1_xboole_0,sK2) | spl6_40),
% 1.54/0.57    inference(avatar_component_clause,[],[f491])).
% 1.54/0.57  fof(f707,plain,(
% 1.54/0.57    spl6_54 | ~spl6_44),
% 1.54/0.57    inference(avatar_split_clause,[],[f644,f562,f685])).
% 1.54/0.57  fof(f685,plain,(
% 1.54/0.57    spl6_54 <=> k1_xboole_0 = sK3),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 1.54/0.57  fof(f644,plain,(
% 1.54/0.57    k1_xboole_0 = sK3 | ~spl6_44),
% 1.54/0.57    inference(subsumption_resolution,[],[f643,f142])).
% 1.54/0.57  fof(f142,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.54/0.57    inference(backward_demodulation,[],[f134,f136])).
% 1.54/0.57  fof(f136,plain,(
% 1.54/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.54/0.57    inference(forward_demodulation,[],[f133,f83])).
% 1.54/0.57  fof(f133,plain,(
% 1.54/0.57    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0))) )),
% 1.54/0.57    inference(resolution,[],[f57,f54])).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f11])).
% 1.54/0.57  fof(f11,axiom,(
% 1.54/0.57    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 1.54/0.57  fof(f134,plain,(
% 1.54/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 1.54/0.57    inference(superposition,[],[f57,f82])).
% 1.54/0.57  fof(f643,plain,(
% 1.54/0.57    ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3 | ~spl6_44),
% 1.54/0.57    inference(resolution,[],[f563,f62])).
% 1.54/0.57  fof(f62,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.54/0.57    inference(cnf_transformation,[],[f40])).
% 1.54/0.57  fof(f40,plain,(
% 1.54/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.57    inference(flattening,[],[f39])).
% 1.54/0.57  fof(f39,plain,(
% 1.54/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.54/0.57    inference(nnf_transformation,[],[f3])).
% 1.54/0.57  fof(f3,axiom,(
% 1.54/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.54/0.57  fof(f690,plain,(
% 1.54/0.57    k1_xboole_0 != sK3 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK3)),
% 1.54/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.57  fof(f674,plain,(
% 1.54/0.57    ~spl6_53 | ~spl6_8 | spl6_28),
% 1.54/0.57    inference(avatar_split_clause,[],[f665,f321,f128,f671])).
% 1.54/0.57  fof(f671,plain,(
% 1.54/0.57    spl6_53 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 1.54/0.57  fof(f128,plain,(
% 1.54/0.57    spl6_8 <=> k1_xboole_0 = sK0),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.54/0.57  fof(f321,plain,(
% 1.54/0.57    spl6_28 <=> sK0 = k1_relat_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.54/0.57  fof(f665,plain,(
% 1.54/0.57    k1_xboole_0 != k1_relat_1(sK3) | (~spl6_8 | spl6_28)),
% 1.54/0.57    inference(forward_demodulation,[],[f322,f130])).
% 1.54/0.57  fof(f130,plain,(
% 1.54/0.57    k1_xboole_0 = sK0 | ~spl6_8),
% 1.54/0.57    inference(avatar_component_clause,[],[f128])).
% 1.54/0.57  fof(f322,plain,(
% 1.54/0.57    sK0 != k1_relat_1(sK3) | spl6_28),
% 1.54/0.57    inference(avatar_component_clause,[],[f321])).
% 1.54/0.57  fof(f638,plain,(
% 1.54/0.57    spl6_44 | ~spl6_7 | ~spl6_10),
% 1.54/0.57    inference(avatar_split_clause,[],[f622,f154,f124,f562])).
% 1.54/0.57  fof(f124,plain,(
% 1.54/0.57    spl6_7 <=> k1_xboole_0 = sK1),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.54/0.57  fof(f154,plain,(
% 1.54/0.57    spl6_10 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.54/0.57  fof(f622,plain,(
% 1.54/0.57    r1_tarski(sK3,k1_xboole_0) | (~spl6_7 | ~spl6_10)),
% 1.54/0.57    inference(forward_demodulation,[],[f618,f82])).
% 1.54/0.57  fof(f618,plain,(
% 1.54/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl6_7 | ~spl6_10)),
% 1.54/0.57    inference(backward_demodulation,[],[f156,f125])).
% 1.54/0.57  fof(f125,plain,(
% 1.54/0.57    k1_xboole_0 = sK1 | ~spl6_7),
% 1.54/0.57    inference(avatar_component_clause,[],[f124])).
% 1.54/0.57  fof(f156,plain,(
% 1.54/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl6_10),
% 1.54/0.57    inference(avatar_component_clause,[],[f154])).
% 1.54/0.57  fof(f613,plain,(
% 1.54/0.57    spl6_48 | ~spl6_15 | ~spl6_28),
% 1.54/0.57    inference(avatar_split_clause,[],[f604,f321,f202,f610])).
% 1.54/0.57  fof(f604,plain,(
% 1.54/0.57    sK0 = k1_relset_1(sK0,sK2,sK3) | (~spl6_15 | ~spl6_28)),
% 1.54/0.57    inference(forward_demodulation,[],[f567,f323])).
% 1.54/0.57  fof(f323,plain,(
% 1.54/0.57    sK0 = k1_relat_1(sK3) | ~spl6_28),
% 1.54/0.57    inference(avatar_component_clause,[],[f321])).
% 1.54/0.57  fof(f567,plain,(
% 1.54/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl6_15),
% 1.54/0.57    inference(resolution,[],[f203,f70])).
% 1.54/0.57  fof(f70,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f29])).
% 1.54/0.57  fof(f29,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f13])).
% 1.54/0.57  fof(f13,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.54/0.57  fof(f592,plain,(
% 1.54/0.57    spl6_46 | ~spl6_9 | ~spl6_17),
% 1.54/0.57    inference(avatar_split_clause,[],[f430,f223,f144,f590])).
% 1.54/0.57  fof(f144,plain,(
% 1.54/0.57    spl6_9 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.54/0.57  fof(f430,plain,(
% 1.54/0.57    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ) | (~spl6_9 | ~spl6_17)),
% 1.54/0.57    inference(forward_demodulation,[],[f428,f146])).
% 1.54/0.57  fof(f146,plain,(
% 1.54/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_9),
% 1.54/0.57    inference(avatar_component_clause,[],[f144])).
% 1.54/0.57  fof(f428,plain,(
% 1.54/0.57    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ) | ~spl6_17),
% 1.54/0.57    inference(resolution,[],[f216,f224])).
% 1.54/0.57  fof(f216,plain,(
% 1.54/0.57    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relat_1(X3) = k1_relset_1(k1_xboole_0,X2,X3)) )),
% 1.54/0.57    inference(superposition,[],[f70,f83])).
% 1.54/0.57  fof(f526,plain,(
% 1.54/0.57    spl6_42 | ~spl6_15),
% 1.54/0.57    inference(avatar_split_clause,[],[f515,f202,f523])).
% 1.54/0.57  fof(f515,plain,(
% 1.54/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | ~spl6_15),
% 1.54/0.57    inference(resolution,[],[f203,f63])).
% 1.54/0.57  fof(f63,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f41])).
% 1.54/0.57  fof(f41,plain,(
% 1.54/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.54/0.57    inference(nnf_transformation,[],[f6])).
% 1.54/0.57  fof(f6,axiom,(
% 1.54/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.54/0.57  fof(f448,plain,(
% 1.54/0.57    spl6_15 | ~spl6_37),
% 1.54/0.57    inference(avatar_split_clause,[],[f447,f444,f202])).
% 1.54/0.57  fof(f444,plain,(
% 1.54/0.57    spl6_37 <=> ! [X0] : (~r1_tarski(sK0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.54/0.57  fof(f447,plain,(
% 1.54/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_37),
% 1.54/0.57    inference(resolution,[],[f445,f80])).
% 1.54/0.57  fof(f80,plain,(
% 1.54/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.54/0.57    inference(equality_resolution,[],[f61])).
% 1.54/0.57  fof(f61,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.54/0.57    inference(cnf_transformation,[],[f40])).
% 1.54/0.57  fof(f445,plain,(
% 1.54/0.57    ( ! [X0] : (~r1_tarski(sK0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl6_37),
% 1.54/0.57    inference(avatar_component_clause,[],[f444])).
% 1.54/0.57  fof(f446,plain,(
% 1.54/0.57    spl6_37 | ~spl6_26 | ~spl6_28 | ~spl6_34),
% 1.54/0.57    inference(avatar_split_clause,[],[f442,f365,f321,f307,f444])).
% 1.54/0.57  fof(f307,plain,(
% 1.54/0.57    spl6_26 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.54/0.57  fof(f365,plain,(
% 1.54/0.57    spl6_34 <=> v1_relat_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.54/0.57  fof(f442,plain,(
% 1.54/0.57    ( ! [X0] : (~r1_tarski(sK0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | (~spl6_26 | ~spl6_28 | ~spl6_34)),
% 1.54/0.57    inference(forward_demodulation,[],[f441,f323])).
% 1.54/0.57  fof(f441,plain,(
% 1.54/0.57    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK3),X0)) ) | (~spl6_26 | ~spl6_34)),
% 1.54/0.57    inference(subsumption_resolution,[],[f312,f367])).
% 1.54/0.57  fof(f367,plain,(
% 1.54/0.57    v1_relat_1(sK3) | ~spl6_34),
% 1.54/0.57    inference(avatar_component_clause,[],[f365])).
% 1.54/0.57  fof(f312,plain,(
% 1.54/0.57    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK3),X0) | ~v1_relat_1(sK3)) ) | ~spl6_26),
% 1.54/0.57    inference(resolution,[],[f309,f68])).
% 1.54/0.57  fof(f68,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f27])).
% 1.54/0.57  fof(f27,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.54/0.57    inference(flattening,[],[f26])).
% 1.54/0.57  fof(f26,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.54/0.57    inference(ennf_transformation,[],[f15])).
% 1.54/0.57  fof(f15,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.54/0.57  fof(f309,plain,(
% 1.54/0.57    r1_tarski(k2_relat_1(sK3),sK2) | ~spl6_26),
% 1.54/0.57    inference(avatar_component_clause,[],[f307])).
% 1.54/0.57  fof(f368,plain,(
% 1.54/0.57    spl6_34 | ~spl6_5),
% 1.54/0.57    inference(avatar_split_clause,[],[f359,f114,f365])).
% 1.54/0.57  fof(f114,plain,(
% 1.54/0.57    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.54/0.57  fof(f359,plain,(
% 1.54/0.57    v1_relat_1(sK3) | ~spl6_5),
% 1.54/0.57    inference(resolution,[],[f150,f116])).
% 1.54/0.57  fof(f116,plain,(
% 1.54/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_5),
% 1.54/0.57    inference(avatar_component_clause,[],[f114])).
% 1.54/0.57  fof(f150,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.54/0.57    inference(resolution,[],[f53,f56])).
% 1.54/0.57  fof(f56,plain,(
% 1.54/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f10])).
% 1.54/0.57  fof(f10,axiom,(
% 1.54/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.54/0.57  fof(f53,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.57  fof(f22,plain,(
% 1.54/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f8])).
% 1.54/0.57  fof(f8,axiom,(
% 1.54/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.54/0.57  fof(f324,plain,(
% 1.54/0.57    spl6_28 | ~spl6_5 | ~spl6_22),
% 1.54/0.57    inference(avatar_split_clause,[],[f318,f277,f114,f321])).
% 1.54/0.57  fof(f277,plain,(
% 1.54/0.57    spl6_22 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.54/0.57  fof(f318,plain,(
% 1.54/0.57    sK0 = k1_relat_1(sK3) | (~spl6_5 | ~spl6_22)),
% 1.54/0.57    inference(forward_demodulation,[],[f212,f279])).
% 1.54/0.57  fof(f279,plain,(
% 1.54/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_22),
% 1.54/0.57    inference(avatar_component_clause,[],[f277])).
% 1.54/0.57  fof(f212,plain,(
% 1.54/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl6_5),
% 1.54/0.57    inference(resolution,[],[f70,f116])).
% 1.54/0.57  fof(f310,plain,(
% 1.54/0.57    spl6_26 | ~spl6_5 | ~spl6_6),
% 1.54/0.57    inference(avatar_split_clause,[],[f295,f119,f114,f307])).
% 1.54/0.57  fof(f119,plain,(
% 1.54/0.57    spl6_6 <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.54/0.57  fof(f295,plain,(
% 1.54/0.57    r1_tarski(k2_relat_1(sK3),sK2) | (~spl6_5 | ~spl6_6)),
% 1.54/0.57    inference(backward_demodulation,[],[f121,f206])).
% 1.54/0.57  fof(f206,plain,(
% 1.54/0.57    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl6_5),
% 1.54/0.57    inference(resolution,[],[f69,f116])).
% 1.54/0.57  fof(f69,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f28])).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f14])).
% 1.54/0.57  fof(f14,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.54/0.57  fof(f121,plain,(
% 1.54/0.57    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) | ~spl6_6),
% 1.54/0.57    inference(avatar_component_clause,[],[f119])).
% 1.54/0.57  fof(f280,plain,(
% 1.54/0.57    spl6_22 | ~spl6_3 | ~spl6_5 | spl6_7),
% 1.54/0.57    inference(avatar_split_clause,[],[f275,f124,f114,f102,f277])).
% 1.54/0.57  fof(f102,plain,(
% 1.54/0.57    spl6_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.54/0.57  fof(f275,plain,(
% 1.54/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl6_3 | ~spl6_5 | spl6_7)),
% 1.54/0.57    inference(subsumption_resolution,[],[f274,f116])).
% 1.54/0.57  fof(f274,plain,(
% 1.54/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl6_3 | spl6_7)),
% 1.54/0.57    inference(subsumption_resolution,[],[f272,f126])).
% 1.54/0.57  fof(f126,plain,(
% 1.54/0.57    k1_xboole_0 != sK1 | spl6_7),
% 1.54/0.57    inference(avatar_component_clause,[],[f124])).
% 1.54/0.57  fof(f272,plain,(
% 1.54/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 1.54/0.57    inference(resolution,[],[f73,f104])).
% 1.54/0.57  fof(f104,plain,(
% 1.54/0.57    v1_funct_2(sK3,sK0,sK1) | ~spl6_3),
% 1.54/0.57    inference(avatar_component_clause,[],[f102])).
% 1.54/0.57  fof(f73,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f44])).
% 1.54/0.57  fof(f231,plain,(
% 1.54/0.57    spl6_17),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f230])).
% 1.54/0.57  fof(f230,plain,(
% 1.54/0.57    $false | spl6_17),
% 1.54/0.57    inference(subsumption_resolution,[],[f228,f142])).
% 1.54/0.57  fof(f228,plain,(
% 1.54/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl6_17),
% 1.54/0.57    inference(resolution,[],[f225,f64])).
% 1.54/0.57  fof(f64,plain,(
% 1.54/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f41])).
% 1.54/0.57  fof(f225,plain,(
% 1.54/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl6_17),
% 1.54/0.57    inference(avatar_component_clause,[],[f223])).
% 1.54/0.57  fof(f205,plain,(
% 1.54/0.57    ~spl6_14 | ~spl6_15 | ~spl6_1),
% 1.54/0.57    inference(avatar_split_clause,[],[f196,f92,f202,f198])).
% 1.54/0.57  fof(f92,plain,(
% 1.54/0.57    spl6_1 <=> v1_funct_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.54/0.57  fof(f196,plain,(
% 1.54/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~spl6_1),
% 1.54/0.57    inference(subsumption_resolution,[],[f50,f94])).
% 1.54/0.57  fof(f94,plain,(
% 1.54/0.57    v1_funct_1(sK3) | ~spl6_1),
% 1.54/0.57    inference(avatar_component_clause,[],[f92])).
% 1.54/0.57  fof(f50,plain,(
% 1.54/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 1.54/0.57    inference(cnf_transformation,[],[f35])).
% 1.54/0.57  fof(f35,plain,(
% 1.54/0.57    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f34])).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f21,plain,(
% 1.54/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.54/0.57    inference(flattening,[],[f20])).
% 1.54/0.57  fof(f20,plain,(
% 1.54/0.57    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.54/0.57    inference(ennf_transformation,[],[f19])).
% 1.54/0.57  fof(f19,negated_conjecture,(
% 1.54/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.54/0.57    inference(negated_conjecture,[],[f18])).
% 1.54/0.57  fof(f18,conjecture,(
% 1.54/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 1.54/0.57  fof(f157,plain,(
% 1.54/0.57    spl6_10 | ~spl6_5),
% 1.54/0.57    inference(avatar_split_clause,[],[f140,f114,f154])).
% 1.54/0.57  fof(f140,plain,(
% 1.54/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl6_5),
% 1.54/0.57    inference(resolution,[],[f63,f116])).
% 1.54/0.57  fof(f147,plain,(
% 1.54/0.57    spl6_9),
% 1.54/0.57    inference(avatar_split_clause,[],[f136,f144])).
% 1.54/0.57  fof(f131,plain,(
% 1.54/0.57    ~spl6_7 | spl6_8),
% 1.54/0.57    inference(avatar_split_clause,[],[f49,f128,f124])).
% 1.54/0.57  fof(f49,plain,(
% 1.54/0.57    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.54/0.57    inference(cnf_transformation,[],[f35])).
% 1.54/0.57  fof(f122,plain,(
% 1.54/0.57    spl6_6),
% 1.54/0.57    inference(avatar_split_clause,[],[f48,f119])).
% 1.54/0.57  fof(f48,plain,(
% 1.54/0.57    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.54/0.57    inference(cnf_transformation,[],[f35])).
% 1.54/0.57  fof(f117,plain,(
% 1.54/0.57    spl6_5),
% 1.54/0.57    inference(avatar_split_clause,[],[f47,f114])).
% 1.54/0.57  fof(f47,plain,(
% 1.54/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.54/0.57    inference(cnf_transformation,[],[f35])).
% 1.54/0.57  fof(f105,plain,(
% 1.54/0.57    spl6_3),
% 1.54/0.57    inference(avatar_split_clause,[],[f46,f102])).
% 1.54/0.57  fof(f46,plain,(
% 1.54/0.57    v1_funct_2(sK3,sK0,sK1)),
% 1.54/0.57    inference(cnf_transformation,[],[f35])).
% 1.54/0.57  fof(f95,plain,(
% 1.54/0.57    spl6_1),
% 1.54/0.57    inference(avatar_split_clause,[],[f45,f92])).
% 1.54/0.57  fof(f45,plain,(
% 1.54/0.57    v1_funct_1(sK3)),
% 1.54/0.57    inference(cnf_transformation,[],[f35])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (32277)------------------------------
% 1.54/0.57  % (32277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (32277)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (32277)Memory used [KB]: 6524
% 1.54/0.57  % (32277)Time elapsed: 0.136 s
% 1.54/0.57  % (32277)------------------------------
% 1.54/0.57  % (32277)------------------------------
% 1.54/0.57  % (32274)Success in time 0.22 s
%------------------------------------------------------------------------------
