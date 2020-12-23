%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0834+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:53 EST 2020

% Result     : Theorem 18.19s
% Output     : Refutation 18.43s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 193 expanded)
%              Number of leaves         :   35 (  89 expanded)
%              Depth                    :    7
%              Number of atoms          :  314 ( 435 expanded)
%              Number of equality atoms :   75 ( 113 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2106,f2115,f2168,f2179,f2353,f2359,f5195,f5220,f7424,f7430,f7531,f7541,f7745,f7753,f7768,f8146,f8174,f8181,f8188,f8276])).

fof(f8276,plain,
    ( ~ spl92_1
    | spl92_342 ),
    inference(avatar_split_clause,[],[f8275,f4967,f2103])).

fof(f2103,plain,
    ( spl92_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_1])])).

fof(f4967,plain,
    ( spl92_342
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_342])])).

fof(f8275,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl92_342 ),
    inference(trivial_inequality_removal,[],[f8274])).

fof(f8274,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl92_342 ),
    inference(superposition,[],[f4968,f1573])).

fof(f1573,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1274])).

fof(f1274,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1224])).

fof(f1224,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f4968,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k1_relat_1(sK2)
    | spl92_342 ),
    inference(avatar_component_clause,[],[f4967])).

fof(f8188,plain,
    ( spl92_523
    | ~ spl92_554 ),
    inference(avatar_split_clause,[],[f7772,f7765,f7472])).

fof(f7472,plain,
    ( spl92_523
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_523])])).

fof(f7765,plain,
    ( spl92_554
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_554])])).

fof(f7772,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl92_554 ),
    inference(resolution,[],[f7767,f1585])).

fof(f1585,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f7767,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl92_554 ),
    inference(avatar_component_clause,[],[f7765])).

fof(f8181,plain,
    ( ~ spl92_10
    | ~ spl92_523
    | spl92_329 ),
    inference(avatar_split_clause,[],[f8177,f4910,f7472,f2160])).

fof(f2160,plain,
    ( spl92_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_10])])).

fof(f4910,plain,
    ( spl92_329
  <=> sK2 = k5_relat_1(sK2,k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_329])])).

fof(f8177,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl92_329 ),
    inference(trivial_inequality_removal,[],[f8176])).

fof(f8176,plain,
    ( sK2 != sK2
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl92_329 ),
    inference(superposition,[],[f4911,f1734])).

fof(f1734,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1409])).

fof(f1409,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1408])).

fof(f1408,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f871])).

fof(f871,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f4911,plain,
    ( sK2 != k5_relat_1(sK2,k6_relat_1(sK1))
    | spl92_329 ),
    inference(avatar_component_clause,[],[f4910])).

fof(f8174,plain,(
    spl92_48 ),
    inference(avatar_contradiction_clause,[],[f8169])).

fof(f8169,plain,
    ( $false
    | spl92_48 ),
    inference(resolution,[],[f2477,f1752])).

fof(f1752,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f668])).

fof(f668,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f2477,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | spl92_48 ),
    inference(avatar_component_clause,[],[f2475])).

fof(f2475,plain,
    ( spl92_48
  <=> v1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_48])])).

fof(f8146,plain,
    ( ~ spl92_10
    | ~ spl92_48
    | spl92_38
    | ~ spl92_329 ),
    inference(avatar_split_clause,[],[f8145,f4910,f2356,f2475,f2160])).

fof(f2356,plain,
    ( spl92_38
  <=> k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_38])])).

fof(f8145,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2)
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl92_329 ),
    inference(forward_demodulation,[],[f8108,f1744])).

fof(f1744,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f8108,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl92_329 ),
    inference(superposition,[],[f1697,f4912])).

fof(f4912,plain,
    ( sK2 = k5_relat_1(sK2,k6_relat_1(sK1))
    | ~ spl92_329 ),
    inference(avatar_component_clause,[],[f4910])).

fof(f1697,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1380])).

fof(f1380,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f784])).

fof(f784,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f7768,plain,
    ( ~ spl92_1
    | spl92_554
    | ~ spl92_552 ),
    inference(avatar_split_clause,[],[f7762,f7750,f7765,f2103])).

fof(f7750,plain,
    ( spl92_552
  <=> k7_relset_1(sK0,sK1,sK2,sK0) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_552])])).

fof(f7762,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl92_552 ),
    inference(superposition,[],[f1575,f7752])).

fof(f7752,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) = k2_relat_1(sK2)
    | ~ spl92_552 ),
    inference(avatar_component_clause,[],[f7750])).

fof(f1575,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1276])).

fof(f1276,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1219])).

fof(f1219,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f7753,plain,
    ( spl92_552
    | ~ spl92_3
    | ~ spl92_280
    | ~ spl92_534 ),
    inference(avatar_split_clause,[],[f7748,f7528,f4280,f2112,f7750])).

fof(f2112,plain,
    ( spl92_3
  <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_3])])).

fof(f4280,plain,
    ( spl92_280
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_280])])).

fof(f7528,plain,
    ( spl92_534
  <=> k2_relset_1(sK0,sK1,sK2) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_534])])).

fof(f7748,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) = k2_relat_1(sK2)
    | ~ spl92_3
    | ~ spl92_280
    | ~ spl92_534 ),
    inference(forward_demodulation,[],[f7747,f4282])).

fof(f4282,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl92_280 ),
    inference(avatar_component_clause,[],[f4280])).

fof(f7747,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) = k9_relat_1(sK2,sK0)
    | ~ spl92_3
    | ~ spl92_534 ),
    inference(forward_demodulation,[],[f2113,f7529])).

fof(f7529,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k9_relat_1(sK2,sK0)
    | ~ spl92_534 ),
    inference(avatar_component_clause,[],[f7528])).

fof(f2113,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)
    | ~ spl92_3 ),
    inference(avatar_component_clause,[],[f2112])).

fof(f7745,plain,
    ( ~ spl92_43
    | ~ spl92_10
    | spl92_280
    | ~ spl92_274 ),
    inference(avatar_split_clause,[],[f7744,f4254,f4280,f2160,f2434])).

fof(f2434,plain,
    ( spl92_43
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_43])])).

fof(f4254,plain,
    ( spl92_274
  <=> sK2 = k5_relat_1(k6_relat_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_274])])).

fof(f7744,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl92_274 ),
    inference(forward_demodulation,[],[f7735,f1745])).

fof(f1745,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f7735,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k2_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl92_274 ),
    inference(superposition,[],[f1890,f4256])).

fof(f4256,plain,
    ( sK2 = k5_relat_1(k6_relat_1(sK0),sK2)
    | ~ spl92_274 ),
    inference(avatar_component_clause,[],[f4254])).

fof(f1890,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1483])).

fof(f1483,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f764])).

fof(f764,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f7541,plain,
    ( ~ spl92_1
    | ~ spl92_280
    | spl92_534 ),
    inference(avatar_split_clause,[],[f7540,f7528,f4280,f2103])).

fof(f7540,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl92_534 ),
    inference(superposition,[],[f7530,f1580])).

fof(f1580,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1279])).

fof(f1279,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1225])).

fof(f1225,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f7530,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | spl92_534 ),
    inference(avatar_component_clause,[],[f7528])).

fof(f7531,plain,
    ( ~ spl92_1
    | ~ spl92_534
    | spl92_3 ),
    inference(avatar_split_clause,[],[f7526,f2112,f7528,f2103])).

fof(f7526,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl92_3 ),
    inference(superposition,[],[f2114,f1574])).

fof(f1574,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1275])).

fof(f1275,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1229])).

fof(f1229,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f2114,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | spl92_3 ),
    inference(avatar_component_clause,[],[f2112])).

fof(f7430,plain,(
    spl92_43 ),
    inference(avatar_contradiction_clause,[],[f7425])).

fof(f7425,plain,
    ( $false
    | spl92_43 ),
    inference(resolution,[],[f2436,f1752])).

fof(f2436,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl92_43 ),
    inference(avatar_component_clause,[],[f2434])).

fof(f7424,plain,
    ( ~ spl92_10
    | ~ spl92_375
    | spl92_274 ),
    inference(avatar_split_clause,[],[f7422,f4254,f5217,f2160])).

fof(f5217,plain,
    ( spl92_375
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_375])])).

fof(f7422,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | spl92_274 ),
    inference(trivial_inequality_removal,[],[f7421])).

fof(f7421,plain,
    ( sK2 != sK2
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | spl92_274 ),
    inference(superposition,[],[f4255,f1733])).

fof(f1733,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1407])).

fof(f1407,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1406])).

fof(f1406,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f869])).

fof(f869,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f4255,plain,
    ( sK2 != k5_relat_1(k6_relat_1(sK0),sK2)
    | spl92_274 ),
    inference(avatar_component_clause,[],[f4254])).

fof(f5220,plain,
    ( spl92_375
    | ~ spl92_372 ),
    inference(avatar_split_clause,[],[f5208,f5192,f5217])).

fof(f5192,plain,
    ( spl92_372
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_372])])).

fof(f5208,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl92_372 ),
    inference(resolution,[],[f5194,f1585])).

fof(f5194,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl92_372 ),
    inference(avatar_component_clause,[],[f5192])).

fof(f5195,plain,
    ( ~ spl92_1
    | spl92_372
    | ~ spl92_342 ),
    inference(avatar_split_clause,[],[f5190,f4967,f5192,f2103])).

fof(f5190,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl92_342 ),
    inference(superposition,[],[f1572,f4969])).

fof(f4969,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl92_342 ),
    inference(avatar_component_clause,[],[f4967])).

fof(f1572,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1273])).

fof(f1273,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1214])).

fof(f1214,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f2359,plain,
    ( ~ spl92_1
    | ~ spl92_38
    | spl92_13 ),
    inference(avatar_split_clause,[],[f2354,f2176,f2356,f2103])).

fof(f2176,plain,
    ( spl92_13
  <=> k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_13])])).

fof(f2354,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl92_13 ),
    inference(superposition,[],[f2178,f1573])).

fof(f2178,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | spl92_13 ),
    inference(avatar_component_clause,[],[f2176])).

fof(f2353,plain,(
    spl92_11 ),
    inference(avatar_contradiction_clause,[],[f2352])).

fof(f2352,plain,
    ( $false
    | spl92_11 ),
    inference(resolution,[],[f2167,f1646])).

fof(f1646,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f2167,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl92_11 ),
    inference(avatar_component_clause,[],[f2165])).

fof(f2165,plain,
    ( spl92_11
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_11])])).

fof(f2179,plain,
    ( ~ spl92_1
    | ~ spl92_13
    | spl92_2 ),
    inference(avatar_split_clause,[],[f2174,f2108,f2176,f2103])).

fof(f2108,plain,
    ( spl92_2
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_2])])).

fof(f2174,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl92_2 ),
    inference(superposition,[],[f2110,f1561])).

fof(f1561,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1264])).

fof(f1264,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1230])).

fof(f1230,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f2110,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl92_2 ),
    inference(avatar_component_clause,[],[f2108])).

fof(f2168,plain,
    ( spl92_10
    | ~ spl92_11
    | ~ spl92_1 ),
    inference(avatar_split_clause,[],[f2127,f2103,f2165,f2160])).

fof(f2127,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2)
    | ~ spl92_1 ),
    inference(resolution,[],[f2105,f1605])).

fof(f1605,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1295])).

fof(f1295,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f2105,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl92_1 ),
    inference(avatar_component_clause,[],[f2103])).

fof(f2115,plain,
    ( ~ spl92_2
    | ~ spl92_3 ),
    inference(avatar_split_clause,[],[f1559,f2112,f2108])).

fof(f1559,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f1263])).

fof(f1263,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1255])).

fof(f1255,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f1254])).

fof(f1254,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f2106,plain,(
    spl92_1 ),
    inference(avatar_split_clause,[],[f1560,f2103])).

fof(f1560,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1263])).
%------------------------------------------------------------------------------
