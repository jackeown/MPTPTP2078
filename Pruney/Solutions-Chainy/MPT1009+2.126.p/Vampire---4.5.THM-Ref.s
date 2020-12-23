%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:44 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 213 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  326 ( 526 expanded)
%              Number of equality atoms :   57 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f83,f94,f98,f104,f108,f118,f128,f147,f181,f197,f240,f316,f324,f451,f454])).

fof(f454,plain,
    ( ~ spl4_4
    | ~ spl4_26
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_26
    | spl4_41 ),
    inference(subsumption_resolution,[],[f452,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f452,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | ~ spl4_4
    | ~ spl4_26
    | spl4_41 ),
    inference(forward_demodulation,[],[f450,f370])).

fof(f370,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f369,f53])).

fof(f53,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f369,plain,
    ( ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f368,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f368,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X0))
        | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) )
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f350,f53])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k9_relat_1(k1_xboole_0,X0))
        | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) )
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(superposition,[],[f129,f239])).

fof(f239,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl4_26
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0))
        | k2_relat_1(sK3) = k9_relat_1(sK3,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f100,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f100,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

% (29145)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f93,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f450,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl4_41
  <=> r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f451,plain,
    ( ~ spl4_41
    | spl4_6
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f345,f238,f102,f449])).

fof(f102,plain,
    ( spl4_6
  <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f345,plain,
    ( ~ r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))
    | spl4_6
    | ~ spl4_26 ),
    inference(superposition,[],[f103,f239])).

fof(f103,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f324,plain,
    ( ~ spl4_4
    | spl4_6
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl4_4
    | spl4_6
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f317,f100])).

fof(f317,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | spl4_6
    | ~ spl4_34 ),
    inference(superposition,[],[f103,f315])).

fof(f315,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl4_34
  <=> k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f316,plain,
    ( spl4_34
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f312,f179,f81,f71,f314])).

fof(f71,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f81,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f179,plain,
    ( spl4_21
  <=> k1_tarski(sK0) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f312,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(equality_resolution,[],[f289])).

fof(f289,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_tarski(sK0)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(superposition,[],[f89,f180])).

fof(f180,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f179])).

fof(f89,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f75,f88])).

fof(f88,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f86,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f86,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1))
    | v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f82,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f82,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | k1_tarski(X0) != k1_relat_1(sK3)
        | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f72,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f72,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f240,plain,
    ( spl4_26
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f232,f195,f238])).

fof(f195,plain,
    ( spl4_22
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f232,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f230,f46])).

fof(f230,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3
    | ~ spl4_22 ),
    inference(resolution,[],[f196,f45])).

fof(f196,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( spl4_22
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f191,f176,f145,f195])).

fof(f145,plain,
    ( spl4_13
  <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f176,plain,
    ( spl4_20
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f191,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f188,f69])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f188,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3)))
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(superposition,[],[f146,f177])).

fof(f177,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f176])).

fof(f146,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f181,plain,
    ( spl4_20
    | spl4_21
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f122,f116,f179,f176])).

fof(f116,plain,
    ( spl4_9
  <=> r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f122,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_9 ),
    inference(resolution,[],[f117,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f117,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f147,plain,
    ( spl4_13
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f134,f126,f145])).

fof(f126,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f134,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl4_10 ),
    inference(resolution,[],[f127,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f127,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( spl4_10
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f90,f81,f71,f126])).

fof(f90,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f74,f88])).

fof(f74,plain,
    ( ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_1 ),
    inference(resolution,[],[f72,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f118,plain,
    ( spl4_9
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f110,f106,f92,f116])).

fof(f106,plain,
    ( spl4_7
  <=> v4_relat_1(sK3,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f110,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f109,f93])).

fof(f109,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f107,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f107,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f84,f81,f106])).

fof(f84,plain,
    ( v4_relat_1(sK3,k1_tarski(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f82,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f104,plain,
    ( ~ spl4_6
    | ~ spl4_3
    | spl4_5 ),
    inference(avatar_split_clause,[],[f99,f96,f81,f102])).

fof(f96,plain,
    ( spl4_5
  <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f99,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl4_3
    | spl4_5 ),
    inference(forward_demodulation,[],[f97,f85])).

fof(f85,plain,
    ( ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f82,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f97,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f37,f96])).

fof(f37,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(f94,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f88,f81,f92])).

fof(f83,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:05:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (29157)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.53  % (29150)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.27/0.53  % (29166)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.53  % (29141)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.53  % (29141)Refutation not found, incomplete strategy% (29141)------------------------------
% 1.27/0.53  % (29141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (29141)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (29141)Memory used [KB]: 1663
% 1.27/0.53  % (29141)Time elapsed: 0.115 s
% 1.27/0.53  % (29141)------------------------------
% 1.27/0.53  % (29141)------------------------------
% 1.27/0.53  % (29157)Refutation not found, incomplete strategy% (29157)------------------------------
% 1.27/0.53  % (29157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (29163)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.53  % (29166)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.54  % (29155)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.27/0.54  % (29142)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.54  % (29150)Refutation not found, incomplete strategy% (29150)------------------------------
% 1.27/0.54  % (29150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (29157)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (29157)Memory used [KB]: 1791
% 1.27/0.54  % (29157)Time elapsed: 0.115 s
% 1.27/0.54  % (29157)------------------------------
% 1.27/0.54  % (29157)------------------------------
% 1.27/0.54  % (29150)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (29150)Memory used [KB]: 10746
% 1.27/0.54  % (29150)Time elapsed: 0.114 s
% 1.27/0.54  % (29150)------------------------------
% 1.27/0.54  % (29150)------------------------------
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f455,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(avatar_sat_refutation,[],[f73,f83,f94,f98,f104,f108,f118,f128,f147,f181,f197,f240,f316,f324,f451,f454])).
% 1.27/0.54  fof(f454,plain,(
% 1.27/0.54    ~spl4_4 | ~spl4_26 | spl4_41),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f453])).
% 1.27/0.54  fof(f453,plain,(
% 1.27/0.54    $false | (~spl4_4 | ~spl4_26 | spl4_41)),
% 1.27/0.54    inference(subsumption_resolution,[],[f452,f65])).
% 1.27/0.54  fof(f65,plain,(
% 1.27/0.54    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 1.27/0.54    inference(equality_resolution,[],[f41])).
% 1.27/0.54  fof(f41,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f6])).
% 1.27/0.54  fof(f6,axiom,(
% 1.27/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.27/0.54  fof(f452,plain,(
% 1.27/0.54    ~r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | (~spl4_4 | ~spl4_26 | spl4_41)),
% 1.27/0.54    inference(forward_demodulation,[],[f450,f370])).
% 1.27/0.54  fof(f370,plain,(
% 1.27/0.54    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_26)),
% 1.27/0.54    inference(forward_demodulation,[],[f369,f53])).
% 1.27/0.54  fof(f53,plain,(
% 1.27/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.27/0.54    inference(cnf_transformation,[],[f13])).
% 1.27/0.54  fof(f13,axiom,(
% 1.27/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.27/0.54  fof(f369,plain,(
% 1.27/0.54    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_26)),
% 1.27/0.54    inference(subsumption_resolution,[],[f368,f46])).
% 1.27/0.54  fof(f46,plain,(
% 1.27/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.27/0.54  fof(f368,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,X0)) | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_26)),
% 1.27/0.54    inference(forward_demodulation,[],[f350,f53])).
% 1.27/0.54  fof(f350,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(k1_xboole_0),k9_relat_1(k1_xboole_0,X0)) | k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_4 | ~spl4_26)),
% 1.27/0.54    inference(superposition,[],[f129,f239])).
% 1.27/0.54  fof(f239,plain,(
% 1.27/0.54    k1_xboole_0 = sK3 | ~spl4_26),
% 1.27/0.54    inference(avatar_component_clause,[],[f238])).
% 1.27/0.54  fof(f238,plain,(
% 1.27/0.54    spl4_26 <=> k1_xboole_0 = sK3),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.27/0.54  fof(f129,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),k9_relat_1(sK3,X0)) | k2_relat_1(sK3) = k9_relat_1(sK3,X0)) ) | ~spl4_4),
% 1.27/0.54    inference(resolution,[],[f100,f45])).
% 1.27/0.54  fof(f45,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.27/0.54    inference(cnf_transformation,[],[f1])).
% 1.27/0.54  fof(f1,axiom,(
% 1.27/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.27/0.54  fof(f100,plain,(
% 1.27/0.54    ( ! [X0] : (r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl4_4),
% 1.27/0.54    inference(resolution,[],[f93,f58])).
% 1.27/0.54  fof(f58,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f31])).
% 1.27/0.54  fof(f31,plain,(
% 1.27/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f12])).
% 1.27/0.54  % (29145)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.27/0.54  fof(f12,axiom,(
% 1.27/0.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 1.27/0.54  fof(f93,plain,(
% 1.27/0.54    v1_relat_1(sK3) | ~spl4_4),
% 1.27/0.54    inference(avatar_component_clause,[],[f92])).
% 1.27/0.54  fof(f92,plain,(
% 1.27/0.54    spl4_4 <=> v1_relat_1(sK3)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.27/0.54  fof(f450,plain,(
% 1.27/0.54    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | spl4_41),
% 1.27/0.54    inference(avatar_component_clause,[],[f449])).
% 1.27/0.54  fof(f449,plain,(
% 1.27/0.54    spl4_41 <=> r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0)))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.27/0.54  fof(f451,plain,(
% 1.27/0.54    ~spl4_41 | spl4_6 | ~spl4_26),
% 1.27/0.54    inference(avatar_split_clause,[],[f345,f238,f102,f449])).
% 1.27/0.54  fof(f102,plain,(
% 1.27/0.54    spl4_6 <=> r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.27/0.54  fof(f345,plain,(
% 1.27/0.54    ~r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_tarski(k1_funct_1(k1_xboole_0,sK0))) | (spl4_6 | ~spl4_26)),
% 1.27/0.54    inference(superposition,[],[f103,f239])).
% 1.27/0.54  fof(f103,plain,(
% 1.27/0.54    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_6),
% 1.27/0.54    inference(avatar_component_clause,[],[f102])).
% 1.27/0.54  fof(f324,plain,(
% 1.27/0.54    ~spl4_4 | spl4_6 | ~spl4_34),
% 1.27/0.54    inference(avatar_contradiction_clause,[],[f323])).
% 1.27/0.54  fof(f323,plain,(
% 1.27/0.54    $false | (~spl4_4 | spl4_6 | ~spl4_34)),
% 1.27/0.54    inference(subsumption_resolution,[],[f317,f100])).
% 1.27/0.54  fof(f317,plain,(
% 1.27/0.54    ~r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | (spl4_6 | ~spl4_34)),
% 1.27/0.54    inference(superposition,[],[f103,f315])).
% 1.27/0.54  fof(f315,plain,(
% 1.27/0.54    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | ~spl4_34),
% 1.27/0.54    inference(avatar_component_clause,[],[f314])).
% 1.27/0.54  fof(f314,plain,(
% 1.27/0.54    spl4_34 <=> k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.27/0.54  fof(f316,plain,(
% 1.27/0.54    spl4_34 | ~spl4_1 | ~spl4_3 | ~spl4_21),
% 1.27/0.54    inference(avatar_split_clause,[],[f312,f179,f81,f71,f314])).
% 1.27/0.54  fof(f71,plain,(
% 1.27/0.54    spl4_1 <=> v1_funct_1(sK3)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.27/0.54  fof(f81,plain,(
% 1.27/0.54    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.27/0.54  fof(f179,plain,(
% 1.27/0.54    spl4_21 <=> k1_tarski(sK0) = k1_relat_1(sK3)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.27/0.54  fof(f312,plain,(
% 1.27/0.54    k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_21)),
% 1.27/0.54    inference(equality_resolution,[],[f289])).
% 1.27/0.54  fof(f289,plain,(
% 1.27/0.54    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl4_1 | ~spl4_3 | ~spl4_21)),
% 1.27/0.54    inference(superposition,[],[f89,f180])).
% 1.27/0.54  fof(f180,plain,(
% 1.27/0.54    k1_tarski(sK0) = k1_relat_1(sK3) | ~spl4_21),
% 1.27/0.54    inference(avatar_component_clause,[],[f179])).
% 1.27/0.54  fof(f89,plain,(
% 1.27/0.54    ( ! [X0] : (k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | (~spl4_1 | ~spl4_3)),
% 1.27/0.54    inference(subsumption_resolution,[],[f75,f88])).
% 1.27/0.54  fof(f88,plain,(
% 1.27/0.54    v1_relat_1(sK3) | ~spl4_3),
% 1.27/0.54    inference(subsumption_resolution,[],[f86,f55])).
% 1.27/0.54  fof(f55,plain,(
% 1.27/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f11])).
% 1.27/0.54  fof(f11,axiom,(
% 1.27/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.27/0.54  fof(f86,plain,(
% 1.27/0.54    ~v1_relat_1(k2_zfmisc_1(k1_tarski(sK0),sK1)) | v1_relat_1(sK3) | ~spl4_3),
% 1.27/0.54    inference(resolution,[],[f82,f54])).
% 1.27/0.54  fof(f54,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f28])).
% 1.27/0.54  fof(f28,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f9])).
% 1.27/0.54  fof(f9,axiom,(
% 1.27/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.27/0.54  fof(f82,plain,(
% 1.27/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~spl4_3),
% 1.27/0.54    inference(avatar_component_clause,[],[f81])).
% 1.27/0.54  fof(f75,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_relat_1(sK3) | k1_tarski(X0) != k1_relat_1(sK3) | k2_relat_1(sK3) = k1_tarski(k1_funct_1(sK3,X0))) ) | ~spl4_1),
% 1.27/0.54    inference(resolution,[],[f72,f47])).
% 1.27/0.54  fof(f47,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f26])).
% 1.27/0.54  fof(f26,plain,(
% 1.27/0.54    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(flattening,[],[f25])).
% 1.27/0.54  fof(f25,plain,(
% 1.27/0.54    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.27/0.54    inference(ennf_transformation,[],[f14])).
% 1.27/0.54  fof(f14,axiom,(
% 1.27/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.27/0.54  fof(f72,plain,(
% 1.27/0.54    v1_funct_1(sK3) | ~spl4_1),
% 1.27/0.54    inference(avatar_component_clause,[],[f71])).
% 1.27/0.54  fof(f240,plain,(
% 1.27/0.54    spl4_26 | ~spl4_22),
% 1.27/0.54    inference(avatar_split_clause,[],[f232,f195,f238])).
% 1.27/0.54  fof(f195,plain,(
% 1.27/0.54    spl4_22 <=> r1_tarski(sK3,k1_xboole_0)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.27/0.54  fof(f232,plain,(
% 1.27/0.54    k1_xboole_0 = sK3 | ~spl4_22),
% 1.27/0.54    inference(subsumption_resolution,[],[f230,f46])).
% 1.27/0.54  fof(f230,plain,(
% 1.27/0.54    ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3 | ~spl4_22),
% 1.27/0.54    inference(resolution,[],[f196,f45])).
% 1.27/0.54  fof(f196,plain,(
% 1.27/0.54    r1_tarski(sK3,k1_xboole_0) | ~spl4_22),
% 1.27/0.54    inference(avatar_component_clause,[],[f195])).
% 1.27/0.54  fof(f197,plain,(
% 1.27/0.54    spl4_22 | ~spl4_13 | ~spl4_20),
% 1.27/0.54    inference(avatar_split_clause,[],[f191,f176,f145,f195])).
% 1.27/0.54  fof(f145,plain,(
% 1.27/0.54    spl4_13 <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.27/0.54  fof(f176,plain,(
% 1.27/0.54    spl4_20 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.27/0.54  fof(f191,plain,(
% 1.27/0.54    r1_tarski(sK3,k1_xboole_0) | (~spl4_13 | ~spl4_20)),
% 1.27/0.54    inference(forward_demodulation,[],[f188,f69])).
% 1.27/0.54  fof(f69,plain,(
% 1.27/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.27/0.54    inference(equality_resolution,[],[f50])).
% 1.27/0.54  fof(f50,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f7])).
% 1.27/0.54  fof(f7,axiom,(
% 1.27/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.27/0.54  fof(f188,plain,(
% 1.27/0.54    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) | (~spl4_13 | ~spl4_20)),
% 1.27/0.54    inference(superposition,[],[f146,f177])).
% 1.27/0.54  fof(f177,plain,(
% 1.27/0.54    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_20),
% 1.27/0.54    inference(avatar_component_clause,[],[f176])).
% 1.27/0.54  fof(f146,plain,(
% 1.27/0.54    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl4_13),
% 1.27/0.54    inference(avatar_component_clause,[],[f145])).
% 1.27/0.54  fof(f181,plain,(
% 1.27/0.54    spl4_20 | spl4_21 | ~spl4_9),
% 1.27/0.54    inference(avatar_split_clause,[],[f122,f116,f179,f176])).
% 1.27/0.54  fof(f116,plain,(
% 1.27/0.54    spl4_9 <=> r1_tarski(k1_relat_1(sK3),k1_tarski(sK0))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.27/0.54  fof(f122,plain,(
% 1.27/0.54    k1_tarski(sK0) = k1_relat_1(sK3) | k1_xboole_0 = k1_relat_1(sK3) | ~spl4_9),
% 1.27/0.54    inference(resolution,[],[f117,f40])).
% 1.27/0.54  fof(f40,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f6])).
% 1.27/0.54  fof(f117,plain,(
% 1.27/0.54    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~spl4_9),
% 1.27/0.54    inference(avatar_component_clause,[],[f116])).
% 1.27/0.54  fof(f147,plain,(
% 1.27/0.54    spl4_13 | ~spl4_10),
% 1.27/0.54    inference(avatar_split_clause,[],[f134,f126,f145])).
% 1.27/0.54  fof(f126,plain,(
% 1.27/0.54    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.27/0.54  fof(f134,plain,(
% 1.27/0.54    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl4_10),
% 1.27/0.54    inference(resolution,[],[f127,f39])).
% 1.27/0.54  fof(f39,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f8])).
% 1.27/0.54  fof(f8,axiom,(
% 1.27/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.27/0.54  fof(f127,plain,(
% 1.27/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_10),
% 1.27/0.54    inference(avatar_component_clause,[],[f126])).
% 1.27/0.54  fof(f128,plain,(
% 1.27/0.54    spl4_10 | ~spl4_1 | ~spl4_3),
% 1.27/0.54    inference(avatar_split_clause,[],[f90,f81,f71,f126])).
% 1.27/0.54  fof(f90,plain,(
% 1.27/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | (~spl4_1 | ~spl4_3)),
% 1.27/0.54    inference(subsumption_resolution,[],[f74,f88])).
% 1.27/0.54  fof(f74,plain,(
% 1.27/0.54    ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_1),
% 1.27/0.54    inference(resolution,[],[f72,f56])).
% 1.27/0.54  fof(f56,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f30])).
% 1.27/0.54  fof(f30,plain,(
% 1.27/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(flattening,[],[f29])).
% 1.27/0.54  fof(f29,plain,(
% 1.27/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.27/0.54    inference(ennf_transformation,[],[f21])).
% 1.27/0.54  fof(f21,plain,(
% 1.27/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 1.27/0.54    inference(pure_predicate_removal,[],[f17])).
% 1.27/0.54  fof(f17,axiom,(
% 1.27/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.27/0.54  fof(f118,plain,(
% 1.27/0.54    spl4_9 | ~spl4_4 | ~spl4_7),
% 1.27/0.54    inference(avatar_split_clause,[],[f110,f106,f92,f116])).
% 1.27/0.54  fof(f106,plain,(
% 1.27/0.54    spl4_7 <=> v4_relat_1(sK3,k1_tarski(sK0))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.27/0.54  fof(f110,plain,(
% 1.27/0.54    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | (~spl4_4 | ~spl4_7)),
% 1.27/0.54    inference(subsumption_resolution,[],[f109,f93])).
% 1.27/0.54  fof(f109,plain,(
% 1.27/0.54    r1_tarski(k1_relat_1(sK3),k1_tarski(sK0)) | ~v1_relat_1(sK3) | ~spl4_7),
% 1.27/0.54    inference(resolution,[],[f107,f60])).
% 1.27/0.54  fof(f60,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f32])).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,axiom,(
% 1.27/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.27/0.54  fof(f107,plain,(
% 1.27/0.54    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl4_7),
% 1.27/0.54    inference(avatar_component_clause,[],[f106])).
% 1.27/0.54  fof(f108,plain,(
% 1.27/0.54    spl4_7 | ~spl4_3),
% 1.27/0.54    inference(avatar_split_clause,[],[f84,f81,f106])).
% 1.27/0.54  fof(f84,plain,(
% 1.27/0.54    v4_relat_1(sK3,k1_tarski(sK0)) | ~spl4_3),
% 1.27/0.54    inference(resolution,[],[f82,f62])).
% 1.27/0.54  fof(f62,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f33])).
% 1.27/0.54  fof(f33,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(ennf_transformation,[],[f22])).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.27/0.54    inference(pure_predicate_removal,[],[f15])).
% 1.27/0.54  fof(f15,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.27/0.54  fof(f104,plain,(
% 1.27/0.54    ~spl4_6 | ~spl4_3 | spl4_5),
% 1.27/0.54    inference(avatar_split_clause,[],[f99,f96,f81,f102])).
% 1.27/0.54  fof(f96,plain,(
% 1.27/0.54    spl4_5 <=> r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.27/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.27/0.54  fof(f99,plain,(
% 1.27/0.54    ~r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | (~spl4_3 | spl4_5)),
% 1.27/0.54    inference(forward_demodulation,[],[f97,f85])).
% 1.27/0.54  fof(f85,plain,(
% 1.27/0.54    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl4_3),
% 1.27/0.54    inference(resolution,[],[f82,f48])).
% 1.27/0.54  fof(f48,plain,(
% 1.27/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f27])).
% 1.27/0.54  fof(f27,plain,(
% 1.27/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.27/0.54    inference(ennf_transformation,[],[f16])).
% 1.27/0.54  fof(f16,axiom,(
% 1.27/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.27/0.54  fof(f97,plain,(
% 1.27/0.54    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) | spl4_5),
% 1.27/0.54    inference(avatar_component_clause,[],[f96])).
% 1.27/0.54  fof(f98,plain,(
% 1.27/0.54    ~spl4_5),
% 1.27/0.54    inference(avatar_split_clause,[],[f37,f96])).
% 1.27/0.54  fof(f37,plain,(
% 1.27/0.54    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 1.27/0.54    inference(cnf_transformation,[],[f24])).
% 1.27/0.54  fof(f24,plain,(
% 1.27/0.54    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 1.27/0.54    inference(flattening,[],[f23])).
% 1.27/0.54  fof(f23,plain,(
% 1.27/0.54    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 1.27/0.54    inference(ennf_transformation,[],[f20])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.27/0.54    inference(pure_predicate_removal,[],[f19])).
% 1.27/0.54  fof(f19,negated_conjecture,(
% 1.27/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.27/0.54    inference(negated_conjecture,[],[f18])).
% 1.27/0.54  fof(f18,conjecture,(
% 1.27/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).
% 1.27/0.54  fof(f94,plain,(
% 1.27/0.54    spl4_4 | ~spl4_3),
% 1.27/0.54    inference(avatar_split_clause,[],[f88,f81,f92])).
% 1.27/0.54  fof(f83,plain,(
% 1.27/0.54    spl4_3),
% 1.27/0.54    inference(avatar_split_clause,[],[f35,f81])).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.27/0.54    inference(cnf_transformation,[],[f24])).
% 1.27/0.54  fof(f73,plain,(
% 1.27/0.54    spl4_1),
% 1.27/0.54    inference(avatar_split_clause,[],[f34,f71])).
% 1.27/0.54  fof(f34,plain,(
% 1.27/0.54    v1_funct_1(sK3)),
% 1.27/0.54    inference(cnf_transformation,[],[f24])).
% 1.27/0.54  % SZS output end Proof for theBenchmark
% 1.27/0.54  % (29166)------------------------------
% 1.27/0.54  % (29166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (29166)Termination reason: Refutation
% 1.27/0.54  
% 1.27/0.54  % (29166)Memory used [KB]: 6396
% 1.27/0.54  % (29166)Time elapsed: 0.121 s
% 1.27/0.54  % (29166)------------------------------
% 1.27/0.54  % (29166)------------------------------
% 1.27/0.54  % (29140)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.54  % (29147)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.27/0.54  % (29139)Success in time 0.173 s
%------------------------------------------------------------------------------
