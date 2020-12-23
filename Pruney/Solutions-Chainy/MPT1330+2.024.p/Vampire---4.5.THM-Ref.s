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
% DateTime   : Thu Dec  3 13:13:58 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 293 expanded)
%              Number of leaves         :   44 ( 131 expanded)
%              Depth                    :    8
%              Number of atoms          :  443 ( 848 expanded)
%              Number of equality atoms :   90 ( 213 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f682,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f109,f118,f150,f155,f162,f167,f173,f179,f190,f199,f208,f217,f246,f359,f455,f457,f485,f548,f608,f611,f665,f671,f680,f681])).

fof(f681,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_partfun1(sK2,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f680,plain,
    ( spl3_73
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f679,f176,f115,f668])).

fof(f668,plain,
    ( spl3_73
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f115,plain,
    ( spl3_8
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f176,plain,
    ( spl3_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f679,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f678,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f678,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f178,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f178,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f671,plain,
    ( spl3_56
    | ~ spl3_73
    | ~ spl3_6
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f666,f662,f106,f668,f450])).

fof(f450,plain,
    ( spl3_56
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f106,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f662,plain,
    ( spl3_72
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f666,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v1_partfun1(sK2,k1_xboole_0)
    | ~ spl3_72 ),
    inference(resolution,[],[f664,f301])).

fof(f301,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_partfun1(X2,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f79,f78])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f664,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f662])).

fof(f665,plain,
    ( spl3_72
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f660,f170,f115,f111,f662])).

fof(f111,plain,
    ( spl3_7
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

% (2349)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f170,plain,
    ( spl3_17
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f660,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f659,f113])).

fof(f113,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f659,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f172,f116])).

fof(f172,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f611,plain,
    ( spl3_40
    | spl3_8
    | ~ spl3_6
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f461,f176,f170,f106,f115,f344])).

fof(f344,plain,
    ( spl3_40
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f461,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_18 ),
    inference(resolution,[],[f178,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f608,plain,
    ( spl3_61
    | ~ spl3_19
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f606,f280,f183,f515])).

fof(f515,plain,
    ( spl3_61
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f183,plain,
    ( spl3_19
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f280,plain,
    ( spl3_31
  <=> sK2 = k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

% (2339)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f606,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_19
    | ~ spl3_31 ),
    inference(superposition,[],[f583,f282])).

fof(f282,plain,
    ( sK2 = k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1)))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f280])).

fof(f583,plain,
    ( ! [X2] : k1_relat_1(k5_relat_1(sK2,k6_partfun1(X2))) = k10_relat_1(sK2,X2)
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f575,f74])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f51,f49])).

fof(f49,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f575,plain,
    ( ! [X2] : k1_relat_1(k5_relat_1(sK2,k6_partfun1(X2))) = k10_relat_1(sK2,k1_relat_1(k6_partfun1(X2)))
    | ~ spl3_19 ),
    inference(resolution,[],[f293,f72])).

fof(f72,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f12])).

% (2348)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f293,plain,
    ( ! [X6] :
        ( ~ v1_relat_1(X6)
        | k1_relat_1(k5_relat_1(sK2,X6)) = k10_relat_1(sK2,k1_relat_1(X6)) )
    | ~ spl3_19 ),
    inference(resolution,[],[f54,f185])).

fof(f185,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f183])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f548,plain,
    ( ~ spl3_61
    | ~ spl3_41
    | spl3_42 ),
    inference(avatar_split_clause,[],[f547,f356,f350,f515])).

fof(f350,plain,
    ( spl3_41
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f356,plain,
    ( spl3_42
  <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f547,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_41
    | spl3_42 ),
    inference(forward_demodulation,[],[f358,f352])).

fof(f352,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f350])).

fof(f358,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f356])).

fof(f485,plain,
    ( spl3_31
    | ~ spl3_19
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f481,f249,f183,f280])).

fof(f249,plain,
    ( spl3_28
  <=> r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f481,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1)))
    | ~ spl3_28 ),
    inference(resolution,[],[f251,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,k6_partfun1(X0)) = X1 ) ),
    inference(definition_unfolding,[],[f57,f49])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f251,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f249])).

fof(f457,plain,
    ( ~ spl3_19
    | spl3_41
    | ~ spl3_22
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f456,f344,f205,f350,f183])).

fof(f205,plain,
    ( spl3_22
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f456,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_40 ),
    inference(resolution,[],[f346,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f346,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f344])).

fof(f455,plain,
    ( ~ spl3_19
    | spl3_28
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f454,f214,f249,f183])).

fof(f214,plain,
    ( spl3_23
  <=> v5_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f454,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl3_23 ),
    inference(resolution,[],[f216,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f216,plain,
    ( v5_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f214])).

fof(f359,plain,
    ( ~ spl3_42
    | ~ spl3_18
    | spl3_27 ),
    inference(avatar_split_clause,[],[f354,f243,f176,f356])).

fof(f243,plain,
    ( spl3_27
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f354,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_18
    | spl3_27 ),
    inference(superposition,[],[f245,f297])).

fof(f297,plain,
    ( ! [X3] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X3) = k10_relat_1(sK2,X3)
    | ~ spl3_18 ),
    inference(resolution,[],[f70,f178])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f245,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f243])).

fof(f246,plain,
    ( ~ spl3_27
    | spl3_3
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f241,f152,f147,f91,f243])).

fof(f91,plain,
    ( spl3_3
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f147,plain,
    ( spl3_13
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f152,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f241,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f240,f149])).

fof(f149,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f240,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f93,f154])).

fof(f154,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f93,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f217,plain,
    ( spl3_23
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f210,f176,f214])).

fof(f210,plain,
    ( v5_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_18 ),
    inference(resolution,[],[f67,f178])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f208,plain,
    ( spl3_22
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f201,f176,f205])).

fof(f201,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_18 ),
    inference(resolution,[],[f66,f178])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f199,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl3_20 ),
    inference(resolution,[],[f189,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f189,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_20
  <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f190,plain,
    ( spl3_19
    | ~ spl3_20
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f181,f176,f187,f183])).

fof(f181,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(resolution,[],[f55,f178])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f179,plain,
    ( spl3_18
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f174,f159,f152,f176])).

fof(f159,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f174,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f161,f154])).

fof(f161,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f173,plain,
    ( spl3_17
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f168,f164,f152,f170])).

fof(f164,plain,
    ( spl3_16
  <=> v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f168,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f166,f154])).

fof(f166,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f167,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f157,f147,f101,f164])).

fof(f101,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f157,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f103,f149])).

fof(f103,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f162,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f156,f147,f96,f159])).

fof(f96,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f156,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f98,f149])).

fof(f98,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f155,plain,
    ( spl3_14
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f145,f86,f152])).

fof(f86,plain,
    ( spl3_2
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f145,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f53,f88])).

fof(f88,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f150,plain,
    ( spl3_13
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f144,f81,f147])).

fof(f81,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f144,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f53,f83])).

fof(f83,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f118,plain,
    ( spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f39,f115,f111])).

fof(f39,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(f109,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f40,f106])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f104,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f41,f101])).

fof(f41,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f42,f96])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f94,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f43,f91])).

fof(f43,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f45,f81])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (2342)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (2337)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (2320)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (2337)Refutation not found, incomplete strategy% (2337)------------------------------
% 0.20/0.52  % (2337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2336)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (2337)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2337)Memory used [KB]: 10746
% 0.20/0.52  % (2337)Time elapsed: 0.060 s
% 0.20/0.52  % (2337)------------------------------
% 0.20/0.52  % (2337)------------------------------
% 0.20/0.52  % (2314)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (2342)Refutation not found, incomplete strategy% (2342)------------------------------
% 0.20/0.52  % (2342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2342)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2342)Memory used [KB]: 10874
% 0.20/0.52  % (2342)Time elapsed: 0.067 s
% 0.20/0.52  % (2342)------------------------------
% 0.20/0.52  % (2342)------------------------------
% 0.20/0.52  % (2319)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (2316)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (2325)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (2317)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (2315)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.53  % (2336)Refutation found. Thanks to Tanya!
% 1.26/0.53  % SZS status Theorem for theBenchmark
% 1.26/0.53  % SZS output start Proof for theBenchmark
% 1.26/0.53  fof(f682,plain,(
% 1.26/0.53    $false),
% 1.26/0.53    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f109,f118,f150,f155,f162,f167,f173,f179,f190,f199,f208,f217,f246,f359,f455,f457,f485,f548,f608,f611,f665,f671,f680,f681])).
% 1.26/0.53  fof(f681,plain,(
% 1.26/0.53    k1_xboole_0 != k2_struct_0(sK0) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_partfun1(sK2,k1_xboole_0)),
% 1.26/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.26/0.53  fof(f680,plain,(
% 1.26/0.53    spl3_73 | ~spl3_8 | ~spl3_18),
% 1.26/0.53    inference(avatar_split_clause,[],[f679,f176,f115,f668])).
% 1.26/0.53  fof(f668,plain,(
% 1.26/0.53    spl3_73 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 1.26/0.53  fof(f115,plain,(
% 1.26/0.53    spl3_8 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.26/0.53  fof(f176,plain,(
% 1.26/0.53    spl3_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.26/0.53  fof(f679,plain,(
% 1.26/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_8 | ~spl3_18)),
% 1.26/0.53    inference(forward_demodulation,[],[f678,f77])).
% 1.26/0.53  fof(f77,plain,(
% 1.26/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.26/0.53    inference(equality_resolution,[],[f65])).
% 1.26/0.53  fof(f65,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f1])).
% 1.26/0.53  fof(f1,axiom,(
% 1.26/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.26/0.53  fof(f678,plain,(
% 1.26/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_8 | ~spl3_18)),
% 1.26/0.53    inference(forward_demodulation,[],[f178,f116])).
% 1.26/0.53  fof(f116,plain,(
% 1.26/0.53    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_8),
% 1.26/0.53    inference(avatar_component_clause,[],[f115])).
% 1.26/0.53  fof(f178,plain,(
% 1.26/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_18),
% 1.26/0.53    inference(avatar_component_clause,[],[f176])).
% 1.26/0.53  fof(f671,plain,(
% 1.26/0.53    spl3_56 | ~spl3_73 | ~spl3_6 | ~spl3_72),
% 1.26/0.53    inference(avatar_split_clause,[],[f666,f662,f106,f668,f450])).
% 1.26/0.53  fof(f450,plain,(
% 1.26/0.53    spl3_56 <=> v1_partfun1(sK2,k1_xboole_0)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 1.26/0.53  fof(f106,plain,(
% 1.26/0.53    spl3_6 <=> v1_funct_1(sK2)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.26/0.53  fof(f662,plain,(
% 1.26/0.53    spl3_72 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 1.26/0.53  fof(f666,plain,(
% 1.26/0.53    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v1_partfun1(sK2,k1_xboole_0) | ~spl3_72),
% 1.26/0.53    inference(resolution,[],[f664,f301])).
% 1.26/0.53  fof(f301,plain,(
% 1.26/0.53    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_partfun1(X2,k1_xboole_0)) )),
% 1.26/0.53    inference(forward_demodulation,[],[f79,f78])).
% 1.26/0.53  fof(f78,plain,(
% 1.26/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.26/0.53    inference(equality_resolution,[],[f64])).
% 1.26/0.53  fof(f64,plain,(
% 1.26/0.53    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f1])).
% 1.26/0.53  fof(f79,plain,(
% 1.26/0.53    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0)) )),
% 1.26/0.53    inference(equality_resolution,[],[f69])).
% 1.26/0.53  fof(f69,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | v1_partfun1(X2,X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f37])).
% 1.26/0.53  fof(f37,plain,(
% 1.26/0.53    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.26/0.53    inference(flattening,[],[f36])).
% 1.26/0.53  fof(f36,plain,(
% 1.26/0.53    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.26/0.53    inference(ennf_transformation,[],[f17])).
% 1.26/0.53  fof(f17,axiom,(
% 1.26/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 1.26/0.53  fof(f664,plain,(
% 1.26/0.53    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl3_72),
% 1.26/0.53    inference(avatar_component_clause,[],[f662])).
% 1.26/0.53  fof(f665,plain,(
% 1.26/0.53    spl3_72 | ~spl3_7 | ~spl3_8 | ~spl3_17),
% 1.26/0.53    inference(avatar_split_clause,[],[f660,f170,f115,f111,f662])).
% 1.26/0.53  fof(f111,plain,(
% 1.26/0.53    spl3_7 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.26/0.53  % (2349)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.26/0.53  fof(f170,plain,(
% 1.26/0.53    spl3_17 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.26/0.53  fof(f660,plain,(
% 1.26/0.53    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_7 | ~spl3_8 | ~spl3_17)),
% 1.26/0.53    inference(forward_demodulation,[],[f659,f113])).
% 1.26/0.53  fof(f113,plain,(
% 1.26/0.53    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_7),
% 1.26/0.53    inference(avatar_component_clause,[],[f111])).
% 1.26/0.53  fof(f659,plain,(
% 1.26/0.53    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | (~spl3_8 | ~spl3_17)),
% 1.26/0.53    inference(forward_demodulation,[],[f172,f116])).
% 1.26/0.53  fof(f172,plain,(
% 1.26/0.53    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_17),
% 1.26/0.53    inference(avatar_component_clause,[],[f170])).
% 1.26/0.53  fof(f611,plain,(
% 1.26/0.53    spl3_40 | spl3_8 | ~spl3_6 | ~spl3_17 | ~spl3_18),
% 1.26/0.53    inference(avatar_split_clause,[],[f461,f176,f170,f106,f115,f344])).
% 1.26/0.53  fof(f344,plain,(
% 1.26/0.53    spl3_40 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.26/0.53  fof(f461,plain,(
% 1.26/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_18),
% 1.26/0.53    inference(resolution,[],[f178,f68])).
% 1.26/0.53  fof(f68,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f37])).
% 1.26/0.53  fof(f608,plain,(
% 1.26/0.53    spl3_61 | ~spl3_19 | ~spl3_31),
% 1.26/0.53    inference(avatar_split_clause,[],[f606,f280,f183,f515])).
% 1.26/0.53  fof(f515,plain,(
% 1.26/0.53    spl3_61 <=> k1_relat_1(sK2) = k10_relat_1(sK2,k2_struct_0(sK1))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 1.26/0.53  fof(f183,plain,(
% 1.26/0.53    spl3_19 <=> v1_relat_1(sK2)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.26/0.53  fof(f280,plain,(
% 1.26/0.53    spl3_31 <=> sK2 = k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1)))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.26/0.53  % (2339)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.26/0.53  fof(f606,plain,(
% 1.26/0.53    k1_relat_1(sK2) = k10_relat_1(sK2,k2_struct_0(sK1)) | (~spl3_19 | ~spl3_31)),
% 1.26/0.53    inference(superposition,[],[f583,f282])).
% 1.26/0.53  fof(f282,plain,(
% 1.26/0.53    sK2 = k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) | ~spl3_31),
% 1.26/0.53    inference(avatar_component_clause,[],[f280])).
% 1.26/0.53  fof(f583,plain,(
% 1.26/0.53    ( ! [X2] : (k1_relat_1(k5_relat_1(sK2,k6_partfun1(X2))) = k10_relat_1(sK2,X2)) ) | ~spl3_19),
% 1.26/0.53    inference(forward_demodulation,[],[f575,f74])).
% 1.26/0.53  fof(f74,plain,(
% 1.26/0.53    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.26/0.53    inference(definition_unfolding,[],[f51,f49])).
% 1.26/0.53  fof(f49,plain,(
% 1.26/0.53    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f16])).
% 1.26/0.53  fof(f16,axiom,(
% 1.26/0.53    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.26/0.53  fof(f51,plain,(
% 1.26/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.26/0.53    inference(cnf_transformation,[],[f9])).
% 1.26/0.53  fof(f9,axiom,(
% 1.26/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.26/0.53  fof(f575,plain,(
% 1.26/0.53    ( ! [X2] : (k1_relat_1(k5_relat_1(sK2,k6_partfun1(X2))) = k10_relat_1(sK2,k1_relat_1(k6_partfun1(X2)))) ) | ~spl3_19),
% 1.26/0.53    inference(resolution,[],[f293,f72])).
% 1.26/0.53  fof(f72,plain,(
% 1.26/0.53    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 1.26/0.53    inference(definition_unfolding,[],[f50,f49])).
% 1.26/0.53  fof(f50,plain,(
% 1.26/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.26/0.53    inference(cnf_transformation,[],[f22])).
% 1.26/0.53  fof(f22,plain,(
% 1.26/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.26/0.53    inference(pure_predicate_removal,[],[f12])).
% 1.26/0.53  % (2348)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.26/0.53  fof(f12,axiom,(
% 1.26/0.53    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.26/0.53  fof(f293,plain,(
% 1.26/0.53    ( ! [X6] : (~v1_relat_1(X6) | k1_relat_1(k5_relat_1(sK2,X6)) = k10_relat_1(sK2,k1_relat_1(X6))) ) | ~spl3_19),
% 1.26/0.53    inference(resolution,[],[f54,f185])).
% 1.26/0.53  fof(f185,plain,(
% 1.26/0.53    v1_relat_1(sK2) | ~spl3_19),
% 1.26/0.53    inference(avatar_component_clause,[],[f183])).
% 1.26/0.53  fof(f54,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.26/0.53    inference(cnf_transformation,[],[f27])).
% 1.26/0.53  fof(f27,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.26/0.53    inference(ennf_transformation,[],[f8])).
% 1.26/0.53  fof(f8,axiom,(
% 1.26/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.26/0.53  fof(f548,plain,(
% 1.26/0.53    ~spl3_61 | ~spl3_41 | spl3_42),
% 1.26/0.53    inference(avatar_split_clause,[],[f547,f356,f350,f515])).
% 1.26/0.53  fof(f350,plain,(
% 1.26/0.53    spl3_41 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.26/0.53  fof(f356,plain,(
% 1.26/0.53    spl3_42 <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.26/0.53  fof(f547,plain,(
% 1.26/0.53    k1_relat_1(sK2) != k10_relat_1(sK2,k2_struct_0(sK1)) | (~spl3_41 | spl3_42)),
% 1.26/0.53    inference(forward_demodulation,[],[f358,f352])).
% 1.26/0.53  fof(f352,plain,(
% 1.26/0.53    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_41),
% 1.26/0.53    inference(avatar_component_clause,[],[f350])).
% 1.26/0.53  fof(f358,plain,(
% 1.26/0.53    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | spl3_42),
% 1.26/0.53    inference(avatar_component_clause,[],[f356])).
% 1.26/0.53  fof(f485,plain,(
% 1.26/0.53    spl3_31 | ~spl3_19 | ~spl3_28),
% 1.26/0.53    inference(avatar_split_clause,[],[f481,f249,f183,f280])).
% 1.26/0.53  fof(f249,plain,(
% 1.26/0.53    spl3_28 <=> r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.26/0.53  fof(f481,plain,(
% 1.26/0.53    ~v1_relat_1(sK2) | sK2 = k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) | ~spl3_28),
% 1.26/0.53    inference(resolution,[],[f251,f75])).
% 1.26/0.53  fof(f75,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X1,k6_partfun1(X0)) = X1) )),
% 1.26/0.53    inference(definition_unfolding,[],[f57,f49])).
% 1.26/0.53  fof(f57,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 1.26/0.53    inference(cnf_transformation,[],[f30])).
% 1.26/0.53  fof(f30,plain,(
% 1.26/0.53    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.26/0.53    inference(flattening,[],[f29])).
% 1.26/0.53  fof(f29,plain,(
% 1.26/0.53    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.26/0.53    inference(ennf_transformation,[],[f10])).
% 1.26/0.53  fof(f10,axiom,(
% 1.26/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.26/0.54  fof(f251,plain,(
% 1.26/0.54    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | ~spl3_28),
% 1.26/0.54    inference(avatar_component_clause,[],[f249])).
% 1.26/0.54  fof(f457,plain,(
% 1.26/0.54    ~spl3_19 | spl3_41 | ~spl3_22 | ~spl3_40),
% 1.26/0.54    inference(avatar_split_clause,[],[f456,f344,f205,f350,f183])).
% 1.26/0.54  fof(f205,plain,(
% 1.26/0.54    spl3_22 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.26/0.54  fof(f456,plain,(
% 1.26/0.54    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_40),
% 1.26/0.54    inference(resolution,[],[f346,f62])).
% 1.26/0.54  fof(f62,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f34])).
% 1.26/0.54  fof(f34,plain,(
% 1.26/0.54    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.26/0.54    inference(flattening,[],[f33])).
% 1.26/0.54  fof(f33,plain,(
% 1.26/0.54    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.26/0.54    inference(ennf_transformation,[],[f15])).
% 1.26/0.54  fof(f15,axiom,(
% 1.26/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.26/0.54  fof(f346,plain,(
% 1.26/0.54    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_40),
% 1.26/0.54    inference(avatar_component_clause,[],[f344])).
% 1.26/0.54  fof(f455,plain,(
% 1.26/0.54    ~spl3_19 | spl3_28 | ~spl3_23),
% 1.26/0.54    inference(avatar_split_clause,[],[f454,f214,f249,f183])).
% 1.26/0.54  fof(f214,plain,(
% 1.26/0.54    spl3_23 <=> v5_relat_1(sK2,k2_struct_0(sK1))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.26/0.54  fof(f454,plain,(
% 1.26/0.54    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | ~v1_relat_1(sK2) | ~spl3_23),
% 1.26/0.54    inference(resolution,[],[f216,f59])).
% 1.26/0.54  fof(f59,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f31])).
% 1.26/0.54  fof(f31,plain,(
% 1.26/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.26/0.54    inference(ennf_transformation,[],[f5])).
% 1.26/0.54  fof(f5,axiom,(
% 1.26/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.26/0.54  fof(f216,plain,(
% 1.26/0.54    v5_relat_1(sK2,k2_struct_0(sK1)) | ~spl3_23),
% 1.26/0.54    inference(avatar_component_clause,[],[f214])).
% 1.26/0.54  fof(f359,plain,(
% 1.26/0.54    ~spl3_42 | ~spl3_18 | spl3_27),
% 1.26/0.54    inference(avatar_split_clause,[],[f354,f243,f176,f356])).
% 1.26/0.54  fof(f243,plain,(
% 1.26/0.54    spl3_27 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.26/0.54  fof(f354,plain,(
% 1.26/0.54    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | (~spl3_18 | spl3_27)),
% 1.26/0.54    inference(superposition,[],[f245,f297])).
% 1.26/0.54  fof(f297,plain,(
% 1.26/0.54    ( ! [X3] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X3) = k10_relat_1(sK2,X3)) ) | ~spl3_18),
% 1.26/0.54    inference(resolution,[],[f70,f178])).
% 1.26/0.54  fof(f70,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f38])).
% 1.26/0.54  fof(f38,plain,(
% 1.26/0.54    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.54    inference(ennf_transformation,[],[f14])).
% 1.26/0.54  fof(f14,axiom,(
% 1.26/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.26/0.54  fof(f245,plain,(
% 1.26/0.54    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_27),
% 1.26/0.54    inference(avatar_component_clause,[],[f243])).
% 1.26/0.54  fof(f246,plain,(
% 1.26/0.54    ~spl3_27 | spl3_3 | ~spl3_13 | ~spl3_14),
% 1.26/0.54    inference(avatar_split_clause,[],[f241,f152,f147,f91,f243])).
% 1.26/0.54  fof(f91,plain,(
% 1.26/0.54    spl3_3 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.26/0.54  fof(f147,plain,(
% 1.26/0.54    spl3_13 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.26/0.54  fof(f152,plain,(
% 1.26/0.54    spl3_14 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.26/0.54  fof(f241,plain,(
% 1.26/0.54    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_3 | ~spl3_13 | ~spl3_14)),
% 1.26/0.54    inference(forward_demodulation,[],[f240,f149])).
% 1.26/0.54  fof(f149,plain,(
% 1.26/0.54    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_13),
% 1.26/0.54    inference(avatar_component_clause,[],[f147])).
% 1.26/0.54  fof(f240,plain,(
% 1.26/0.54    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (spl3_3 | ~spl3_14)),
% 1.26/0.54    inference(forward_demodulation,[],[f93,f154])).
% 1.26/0.54  fof(f154,plain,(
% 1.26/0.54    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_14),
% 1.26/0.54    inference(avatar_component_clause,[],[f152])).
% 1.26/0.54  fof(f93,plain,(
% 1.26/0.54    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_3),
% 1.26/0.54    inference(avatar_component_clause,[],[f91])).
% 1.26/0.54  fof(f217,plain,(
% 1.26/0.54    spl3_23 | ~spl3_18),
% 1.26/0.54    inference(avatar_split_clause,[],[f210,f176,f214])).
% 1.26/0.54  fof(f210,plain,(
% 1.26/0.54    v5_relat_1(sK2,k2_struct_0(sK1)) | ~spl3_18),
% 1.26/0.54    inference(resolution,[],[f67,f178])).
% 1.26/0.54  fof(f67,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f35])).
% 1.26/0.54  fof(f35,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.26/0.54    inference(ennf_transformation,[],[f13])).
% 1.26/0.54  fof(f13,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.26/0.54  fof(f208,plain,(
% 1.26/0.54    spl3_22 | ~spl3_18),
% 1.26/0.54    inference(avatar_split_clause,[],[f201,f176,f205])).
% 1.26/0.54  fof(f201,plain,(
% 1.26/0.54    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_18),
% 1.26/0.54    inference(resolution,[],[f66,f178])).
% 1.26/0.54  fof(f66,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f35])).
% 1.26/0.54  fof(f199,plain,(
% 1.26/0.54    spl3_20),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f198])).
% 1.26/0.54  fof(f198,plain,(
% 1.26/0.54    $false | spl3_20),
% 1.26/0.54    inference(resolution,[],[f189,f56])).
% 1.26/0.54  fof(f56,plain,(
% 1.26/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f6])).
% 1.26/0.54  fof(f6,axiom,(
% 1.26/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.26/0.54  fof(f189,plain,(
% 1.26/0.54    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_20),
% 1.26/0.54    inference(avatar_component_clause,[],[f187])).
% 1.26/0.54  fof(f187,plain,(
% 1.26/0.54    spl3_20 <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.26/0.54  fof(f190,plain,(
% 1.26/0.54    spl3_19 | ~spl3_20 | ~spl3_18),
% 1.26/0.54    inference(avatar_split_clause,[],[f181,f176,f187,f183])).
% 1.26/0.54  fof(f181,plain,(
% 1.26/0.54    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2) | ~spl3_18),
% 1.26/0.54    inference(resolution,[],[f55,f178])).
% 1.26/0.54  fof(f55,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f28])).
% 1.26/0.54  fof(f28,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.26/0.54    inference(ennf_transformation,[],[f4])).
% 1.26/0.54  fof(f4,axiom,(
% 1.26/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.26/0.54  fof(f179,plain,(
% 1.26/0.54    spl3_18 | ~spl3_14 | ~spl3_15),
% 1.26/0.54    inference(avatar_split_clause,[],[f174,f159,f152,f176])).
% 1.26/0.54  fof(f159,plain,(
% 1.26/0.54    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.26/0.54  fof(f174,plain,(
% 1.26/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_14 | ~spl3_15)),
% 1.26/0.54    inference(forward_demodulation,[],[f161,f154])).
% 1.26/0.54  fof(f161,plain,(
% 1.26/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_15),
% 1.26/0.54    inference(avatar_component_clause,[],[f159])).
% 1.26/0.54  fof(f173,plain,(
% 1.26/0.54    spl3_17 | ~spl3_14 | ~spl3_16),
% 1.26/0.54    inference(avatar_split_clause,[],[f168,f164,f152,f170])).
% 1.26/0.54  fof(f164,plain,(
% 1.26/0.54    spl3_16 <=> v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.26/0.54  fof(f168,plain,(
% 1.26/0.54    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_14 | ~spl3_16)),
% 1.26/0.54    inference(forward_demodulation,[],[f166,f154])).
% 1.26/0.54  fof(f166,plain,(
% 1.26/0.54    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_16),
% 1.26/0.54    inference(avatar_component_clause,[],[f164])).
% 1.26/0.54  fof(f167,plain,(
% 1.26/0.54    spl3_16 | ~spl3_5 | ~spl3_13),
% 1.26/0.54    inference(avatar_split_clause,[],[f157,f147,f101,f164])).
% 1.26/0.54  fof(f101,plain,(
% 1.26/0.54    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.26/0.54  fof(f157,plain,(
% 1.26/0.54    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl3_5 | ~spl3_13)),
% 1.26/0.54    inference(backward_demodulation,[],[f103,f149])).
% 1.26/0.54  fof(f103,plain,(
% 1.26/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 1.26/0.54    inference(avatar_component_clause,[],[f101])).
% 1.26/0.54  fof(f162,plain,(
% 1.26/0.54    spl3_15 | ~spl3_4 | ~spl3_13),
% 1.26/0.54    inference(avatar_split_clause,[],[f156,f147,f96,f159])).
% 1.26/0.54  fof(f96,plain,(
% 1.26/0.54    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.26/0.54  fof(f156,plain,(
% 1.26/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | (~spl3_4 | ~spl3_13)),
% 1.26/0.54    inference(backward_demodulation,[],[f98,f149])).
% 1.26/0.54  fof(f98,plain,(
% 1.26/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 1.26/0.54    inference(avatar_component_clause,[],[f96])).
% 1.26/0.54  fof(f155,plain,(
% 1.26/0.54    spl3_14 | ~spl3_2),
% 1.26/0.54    inference(avatar_split_clause,[],[f145,f86,f152])).
% 1.26/0.54  fof(f86,plain,(
% 1.26/0.54    spl3_2 <=> l1_struct_0(sK1)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.26/0.54  fof(f145,plain,(
% 1.26/0.54    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_2),
% 1.26/0.54    inference(resolution,[],[f53,f88])).
% 1.26/0.54  fof(f88,plain,(
% 1.26/0.54    l1_struct_0(sK1) | ~spl3_2),
% 1.26/0.54    inference(avatar_component_clause,[],[f86])).
% 1.26/0.54  fof(f53,plain,(
% 1.26/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f26])).
% 1.26/0.54  fof(f26,plain,(
% 1.26/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.26/0.54    inference(ennf_transformation,[],[f19])).
% 1.26/0.54  fof(f19,axiom,(
% 1.26/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.26/0.54  fof(f150,plain,(
% 1.26/0.54    spl3_13 | ~spl3_1),
% 1.26/0.54    inference(avatar_split_clause,[],[f144,f81,f147])).
% 1.26/0.54  fof(f81,plain,(
% 1.26/0.54    spl3_1 <=> l1_struct_0(sK0)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.26/0.54  fof(f144,plain,(
% 1.26/0.54    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_1),
% 1.26/0.54    inference(resolution,[],[f53,f83])).
% 1.26/0.54  fof(f83,plain,(
% 1.26/0.54    l1_struct_0(sK0) | ~spl3_1),
% 1.26/0.54    inference(avatar_component_clause,[],[f81])).
% 1.26/0.54  fof(f118,plain,(
% 1.26/0.54    spl3_7 | ~spl3_8),
% 1.26/0.54    inference(avatar_split_clause,[],[f39,f115,f111])).
% 1.26/0.54  fof(f39,plain,(
% 1.26/0.54    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.26/0.54    inference(cnf_transformation,[],[f25])).
% 1.26/0.54  fof(f25,plain,(
% 1.26/0.54    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.26/0.54    inference(flattening,[],[f24])).
% 1.26/0.54  fof(f24,plain,(
% 1.26/0.54    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.26/0.54    inference(ennf_transformation,[],[f21])).
% 1.26/0.54  fof(f21,negated_conjecture,(
% 1.26/0.54    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 1.26/0.54    inference(negated_conjecture,[],[f20])).
% 1.26/0.54  fof(f20,conjecture,(
% 1.26/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).
% 1.26/0.54  fof(f109,plain,(
% 1.26/0.54    spl3_6),
% 1.26/0.54    inference(avatar_split_clause,[],[f40,f106])).
% 1.26/0.54  fof(f40,plain,(
% 1.26/0.54    v1_funct_1(sK2)),
% 1.26/0.54    inference(cnf_transformation,[],[f25])).
% 1.26/0.54  fof(f104,plain,(
% 1.26/0.54    spl3_5),
% 1.26/0.54    inference(avatar_split_clause,[],[f41,f101])).
% 1.26/0.54  fof(f41,plain,(
% 1.26/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.26/0.54    inference(cnf_transformation,[],[f25])).
% 1.26/0.54  fof(f99,plain,(
% 1.26/0.54    spl3_4),
% 1.26/0.54    inference(avatar_split_clause,[],[f42,f96])).
% 1.26/0.54  fof(f42,plain,(
% 1.26/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.26/0.54    inference(cnf_transformation,[],[f25])).
% 1.26/0.54  fof(f94,plain,(
% 1.26/0.54    ~spl3_3),
% 1.26/0.54    inference(avatar_split_clause,[],[f43,f91])).
% 1.26/0.54  fof(f43,plain,(
% 1.26/0.54    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 1.26/0.54    inference(cnf_transformation,[],[f25])).
% 1.26/0.54  fof(f89,plain,(
% 1.26/0.54    spl3_2),
% 1.26/0.54    inference(avatar_split_clause,[],[f44,f86])).
% 1.26/0.54  fof(f44,plain,(
% 1.26/0.54    l1_struct_0(sK1)),
% 1.26/0.54    inference(cnf_transformation,[],[f25])).
% 1.26/0.54  fof(f84,plain,(
% 1.26/0.54    spl3_1),
% 1.26/0.54    inference(avatar_split_clause,[],[f45,f81])).
% 1.26/0.54  fof(f45,plain,(
% 1.26/0.54    l1_struct_0(sK0)),
% 1.26/0.54    inference(cnf_transformation,[],[f25])).
% 1.26/0.54  % SZS output end Proof for theBenchmark
% 1.26/0.54  % (2336)------------------------------
% 1.26/0.54  % (2336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (2336)Termination reason: Refutation
% 1.26/0.54  
% 1.26/0.54  % (2336)Memory used [KB]: 11257
% 1.26/0.54  % (2336)Time elapsed: 0.089 s
% 1.26/0.54  % (2336)------------------------------
% 1.26/0.54  % (2336)------------------------------
% 1.26/0.54  % (2346)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.26/0.54  % (2309)Success in time 0.179 s
%------------------------------------------------------------------------------
