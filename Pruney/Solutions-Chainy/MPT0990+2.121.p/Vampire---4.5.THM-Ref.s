%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:49 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 302 expanded)
%              Number of leaves         :   45 ( 130 expanded)
%              Depth                    :   10
%              Number of atoms          :  581 (1460 expanded)
%              Number of equality atoms :  106 ( 375 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1026,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f109,f134,f139,f144,f149,f154,f166,f170,f179,f183,f198,f203,f261,f324,f355,f381,f782,f786,f869,f875,f882,f885,f1022,f1025])).

fof(f1025,plain,
    ( ~ spl4_16
    | ~ spl4_18
    | spl4_54 ),
    inference(avatar_contradiction_clause,[],[f1023])).

fof(f1023,plain,
    ( $false
    | ~ spl4_16
    | ~ spl4_18
    | spl4_54 ),
    inference(unit_resulting_resolution,[],[f178,f202,f1021,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1021,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_54 ),
    inference(avatar_component_clause,[],[f1019])).

fof(f1019,plain,
    ( spl4_54
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f202,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl4_18
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f178,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_16
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1022,plain,
    ( ~ spl4_16
    | ~ spl4_54
    | spl4_8
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f973,f866,f131,f1019,f176])).

fof(f131,plain,
    ( spl4_8
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f866,plain,
    ( spl4_46
  <=> k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f973,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_46 ),
    inference(superposition,[],[f868,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f83,f72])).

fof(f72,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f868,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f866])).

fof(f885,plain,
    ( ~ spl4_14
    | ~ spl4_17
    | spl4_48 ),
    inference(avatar_contradiction_clause,[],[f883])).

fof(f883,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_17
    | spl4_48 ),
    inference(unit_resulting_resolution,[],[f165,f197,f881,f84])).

fof(f881,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_48 ),
    inference(avatar_component_clause,[],[f879])).

fof(f879,plain,
    ( spl4_48
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f197,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl4_17
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f165,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl4_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f882,plain,
    ( ~ spl4_14
    | ~ spl4_48
    | spl4_47 ),
    inference(avatar_split_clause,[],[f877,f872,f879,f163])).

fof(f872,plain,
    ( spl4_47
  <=> r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f877,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | spl4_47 ),
    inference(superposition,[],[f874,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f874,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | spl4_47 ),
    inference(avatar_component_clause,[],[f872])).

fof(f875,plain,
    ( ~ spl4_14
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_47
    | spl4_45 ),
    inference(avatar_split_clause,[],[f870,f862,f872,f106,f96,f163])).

fof(f96,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f106,plain,
    ( spl4_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f862,plain,
    ( spl4_45
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f870,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_45 ),
    inference(superposition,[],[f864,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f864,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | spl4_45 ),
    inference(avatar_component_clause,[],[f862])).

fof(f869,plain,
    ( ~ spl4_43
    | ~ spl4_45
    | spl4_46
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f790,f779,f866,f862,f775])).

fof(f775,plain,
    ( spl4_43
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f779,plain,
    ( spl4_44
  <=> k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f790,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_44 ),
    inference(superposition,[],[f781,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f80,f72])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f781,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f779])).

fof(f786,plain,
    ( ~ spl4_1
    | ~ spl4_14
    | spl4_43 ),
    inference(avatar_contradiction_clause,[],[f783])).

fof(f783,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_14
    | spl4_43 ),
    inference(unit_resulting_resolution,[],[f165,f98,f777,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f777,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_43 ),
    inference(avatar_component_clause,[],[f775])).

fof(f98,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f782,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_43
    | ~ spl4_14
    | ~ spl4_16
    | spl4_44
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f528,f340,f258,f779,f176,f163,f775,f106,f96])).

fof(f258,plain,
    ( spl4_24
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f340,plain,
    ( spl4_30
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f528,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f501,f260])).

fof(f260,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f258])).

fof(f501,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl4_30 ),
    inference(superposition,[],[f301,f342])).

fof(f342,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f340])).

fof(f301,plain,(
    ! [X14,X13] :
      ( k5_relat_1(k2_funct_1(X13),k5_relat_1(X13,X14)) = k5_relat_1(k6_partfun1(k2_relat_1(X13)),X14)
      | ~ v1_relat_1(X14)
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(k2_funct_1(X13))
      | ~ v2_funct_1(X13)
      | ~ v1_funct_1(X13) ) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,(
    ! [X14,X13] :
      ( k5_relat_1(k2_funct_1(X13),k5_relat_1(X13,X14)) = k5_relat_1(k6_partfun1(k2_relat_1(X13)),X14)
      | ~ v1_relat_1(X14)
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(k2_funct_1(X13))
      | ~ v2_funct_1(X13)
      | ~ v1_funct_1(X13)
      | ~ v1_relat_1(X13) ) ),
    inference(superposition,[],[f76,f89])).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f72])).

fof(f64,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

% (18676)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f381,plain,
    ( ~ spl4_1
    | ~ spl4_9
    | ~ spl4_2
    | ~ spl4_10
    | spl4_30
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f356,f321,f340,f141,f101,f136,f96])).

fof(f136,plain,
    ( spl4_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f101,plain,
    ( spl4_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f141,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f321,plain,
    ( spl4_27
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f356,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_27 ),
    inference(superposition,[],[f323,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f323,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f321])).

fof(f355,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | spl4_26 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | spl4_26 ),
    inference(unit_resulting_resolution,[],[f98,f103,f138,f143,f319,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f319,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl4_26
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f143,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f103,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f324,plain,
    ( ~ spl4_26
    | spl4_27
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f314,f151,f321,f317])).

fof(f151,plain,
    ( spl4_12
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f314,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_12 ),
    inference(resolution,[],[f311,f153])).

fof(f153,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f311,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f68,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f261,plain,
    ( ~ spl4_9
    | spl4_24
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f249,f146,f258,f136])).

fof(f146,plain,
    ( spl4_11
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f249,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(superposition,[],[f77,f148])).

fof(f148,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f203,plain,
    ( spl4_18
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f192,f141,f200])).

fof(f192,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl4_10 ),
    inference(resolution,[],[f87,f143])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f198,plain,
    ( spl4_17
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f191,f136,f195])).

fof(f191,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f87,f138])).

fof(f183,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl4_15 ),
    inference(unit_resulting_resolution,[],[f79,f174])).

fof(f174,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_15
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f179,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f156,f141,f176,f172])).

fof(f156,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_10 ),
    inference(resolution,[],[f78,f143])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f170,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f79,f161])).

fof(f161,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_13
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f166,plain,
    ( ~ spl4_13
    | spl4_14
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f155,f136,f163,f159])).

fof(f155,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_9 ),
    inference(resolution,[],[f78,f138])).

fof(f154,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f58,f151])).

fof(f58,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f47,f46])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f149,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f57,f146])).

fof(f57,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f144,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f56,f141])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f139,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f53,f136])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f134,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f62,f131])).

fof(f62,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f48])).

fof(f109,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f59,f106])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f104,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f54,f101])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f99,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f51,f96])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:40:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (18674)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (18654)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (18655)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (18656)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (18657)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (18662)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (18671)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (18661)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (18652)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (18651)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (18659)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (18665)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (18660)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (18679)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (18675)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (18680)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (18678)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (18672)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (18667)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (18653)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (18673)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (18667)Refutation not found, incomplete strategy% (18667)------------------------------
% 0.21/0.55  % (18667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18670)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (18667)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18667)Memory used [KB]: 10746
% 0.21/0.55  % (18667)Time elapsed: 0.138 s
% 0.21/0.55  % (18667)------------------------------
% 0.21/0.55  % (18667)------------------------------
% 1.46/0.55  % (18658)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.46/0.55  % (18663)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.46/0.55  % (18666)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.46/0.55  % (18664)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.55  % (18674)Refutation found. Thanks to Tanya!
% 1.46/0.55  % SZS status Theorem for theBenchmark
% 1.46/0.56  % SZS output start Proof for theBenchmark
% 1.46/0.56  fof(f1026,plain,(
% 1.46/0.56    $false),
% 1.46/0.56    inference(avatar_sat_refutation,[],[f99,f104,f109,f134,f139,f144,f149,f154,f166,f170,f179,f183,f198,f203,f261,f324,f355,f381,f782,f786,f869,f875,f882,f885,f1022,f1025])).
% 1.46/0.56  fof(f1025,plain,(
% 1.46/0.56    ~spl4_16 | ~spl4_18 | spl4_54),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f1023])).
% 1.46/0.56  fof(f1023,plain,(
% 1.46/0.56    $false | (~spl4_16 | ~spl4_18 | spl4_54)),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f178,f202,f1021,f84])).
% 1.46/0.56  fof(f84,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f50])).
% 1.46/0.56  fof(f50,plain,(
% 1.46/0.56    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.46/0.56    inference(nnf_transformation,[],[f43])).
% 1.46/0.56  fof(f43,plain,(
% 1.46/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.46/0.56    inference(ennf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.46/0.56  fof(f1021,plain,(
% 1.46/0.56    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_54),
% 1.46/0.56    inference(avatar_component_clause,[],[f1019])).
% 1.46/0.56  fof(f1019,plain,(
% 1.46/0.56    spl4_54 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 1.46/0.56  fof(f202,plain,(
% 1.46/0.56    v4_relat_1(sK3,sK1) | ~spl4_18),
% 1.46/0.56    inference(avatar_component_clause,[],[f200])).
% 1.46/0.56  fof(f200,plain,(
% 1.46/0.56    spl4_18 <=> v4_relat_1(sK3,sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.46/0.56  fof(f178,plain,(
% 1.46/0.56    v1_relat_1(sK3) | ~spl4_16),
% 1.46/0.56    inference(avatar_component_clause,[],[f176])).
% 1.46/0.56  fof(f176,plain,(
% 1.46/0.56    spl4_16 <=> v1_relat_1(sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.46/0.56  fof(f1022,plain,(
% 1.46/0.56    ~spl4_16 | ~spl4_54 | spl4_8 | ~spl4_46),
% 1.46/0.56    inference(avatar_split_clause,[],[f973,f866,f131,f1019,f176])).
% 1.46/0.56  fof(f131,plain,(
% 1.46/0.56    spl4_8 <=> k2_funct_1(sK2) = sK3),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.46/0.56  fof(f866,plain,(
% 1.46/0.56    spl4_46 <=> k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.46/0.56  fof(f973,plain,(
% 1.46/0.56    k2_funct_1(sK2) = sK3 | ~r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl4_46),
% 1.46/0.56    inference(superposition,[],[f868,f92])).
% 1.46/0.56  fof(f92,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.46/0.56    inference(definition_unfolding,[],[f83,f72])).
% 1.46/0.56  fof(f72,plain,(
% 1.46/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,axiom,(
% 1.46/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.46/0.56  fof(f83,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f42,plain,(
% 1.46/0.56    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.46/0.56    inference(flattening,[],[f41])).
% 1.46/0.56  fof(f41,plain,(
% 1.46/0.56    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.46/0.56    inference(ennf_transformation,[],[f7])).
% 1.46/0.56  fof(f7,axiom,(
% 1.46/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 1.46/0.56  fof(f868,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_46),
% 1.46/0.56    inference(avatar_component_clause,[],[f866])).
% 1.46/0.56  fof(f885,plain,(
% 1.46/0.56    ~spl4_14 | ~spl4_17 | spl4_48),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f883])).
% 1.46/0.56  fof(f883,plain,(
% 1.46/0.56    $false | (~spl4_14 | ~spl4_17 | spl4_48)),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f165,f197,f881,f84])).
% 1.46/0.56  fof(f881,plain,(
% 1.46/0.56    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_48),
% 1.46/0.56    inference(avatar_component_clause,[],[f879])).
% 1.46/0.56  fof(f879,plain,(
% 1.46/0.56    spl4_48 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 1.46/0.56  fof(f197,plain,(
% 1.46/0.56    v4_relat_1(sK2,sK0) | ~spl4_17),
% 1.46/0.56    inference(avatar_component_clause,[],[f195])).
% 1.46/0.56  fof(f195,plain,(
% 1.46/0.56    spl4_17 <=> v4_relat_1(sK2,sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.46/0.56  fof(f165,plain,(
% 1.46/0.56    v1_relat_1(sK2) | ~spl4_14),
% 1.46/0.56    inference(avatar_component_clause,[],[f163])).
% 1.46/0.56  fof(f163,plain,(
% 1.46/0.56    spl4_14 <=> v1_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.46/0.56  fof(f882,plain,(
% 1.46/0.56    ~spl4_14 | ~spl4_48 | spl4_47),
% 1.46/0.56    inference(avatar_split_clause,[],[f877,f872,f879,f163])).
% 1.46/0.56  fof(f872,plain,(
% 1.46/0.56    spl4_47 <=> r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.46/0.56  fof(f877,plain,(
% 1.46/0.56    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | spl4_47),
% 1.46/0.56    inference(superposition,[],[f874,f82])).
% 1.46/0.56  fof(f82,plain,(
% 1.46/0.56    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f40])).
% 1.46/0.56  fof(f40,plain,(
% 1.46/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.46/0.56  fof(f874,plain,(
% 1.46/0.56    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | spl4_47),
% 1.46/0.56    inference(avatar_component_clause,[],[f872])).
% 1.46/0.56  fof(f875,plain,(
% 1.46/0.56    ~spl4_14 | ~spl4_1 | ~spl4_3 | ~spl4_47 | spl4_45),
% 1.46/0.56    inference(avatar_split_clause,[],[f870,f862,f872,f106,f96,f163])).
% 1.46/0.56  fof(f96,plain,(
% 1.46/0.56    spl4_1 <=> v1_funct_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.46/0.56  fof(f106,plain,(
% 1.46/0.56    spl4_3 <=> v2_funct_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.46/0.56  fof(f862,plain,(
% 1.46/0.56    spl4_45 <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.46/0.56  fof(f870,plain,(
% 1.46/0.56    ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_45),
% 1.46/0.56    inference(superposition,[],[f864,f65])).
% 1.46/0.56  fof(f65,plain,(
% 1.46/0.56    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f9])).
% 1.46/0.56  fof(f9,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.46/0.56  fof(f864,plain,(
% 1.46/0.56    ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | spl4_45),
% 1.46/0.56    inference(avatar_component_clause,[],[f862])).
% 1.46/0.56  fof(f869,plain,(
% 1.46/0.56    ~spl4_43 | ~spl4_45 | spl4_46 | ~spl4_44),
% 1.46/0.56    inference(avatar_split_clause,[],[f790,f779,f866,f862,f775])).
% 1.46/0.56  fof(f775,plain,(
% 1.46/0.56    spl4_43 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.46/0.56  fof(f779,plain,(
% 1.46/0.56    spl4_44 <=> k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.46/0.56  fof(f790,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_44),
% 1.46/0.56    inference(superposition,[],[f781,f91])).
% 1.46/0.56  fof(f91,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.46/0.56    inference(definition_unfolding,[],[f80,f72])).
% 1.46/0.56  fof(f80,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f39])).
% 1.46/0.56  fof(f39,plain,(
% 1.46/0.56    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.46/0.56    inference(flattening,[],[f38])).
% 1.46/0.56  fof(f38,plain,(
% 1.46/0.56    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,axiom,(
% 1.46/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.46/0.56  fof(f781,plain,(
% 1.46/0.56    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_44),
% 1.46/0.56    inference(avatar_component_clause,[],[f779])).
% 1.46/0.56  fof(f786,plain,(
% 1.46/0.56    ~spl4_1 | ~spl4_14 | spl4_43),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f783])).
% 1.46/0.56  fof(f783,plain,(
% 1.46/0.56    $false | (~spl4_1 | ~spl4_14 | spl4_43)),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f165,f98,f777,f66])).
% 1.46/0.56  fof(f66,plain,(
% 1.46/0.56    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f28])).
% 1.46/0.56  fof(f28,plain,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f27])).
% 1.46/0.56  fof(f27,plain,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f10])).
% 1.46/0.56  fof(f10,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.46/0.56  fof(f777,plain,(
% 1.46/0.56    ~v1_relat_1(k2_funct_1(sK2)) | spl4_43),
% 1.46/0.56    inference(avatar_component_clause,[],[f775])).
% 1.46/0.56  fof(f98,plain,(
% 1.46/0.56    v1_funct_1(sK2) | ~spl4_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f96])).
% 1.46/0.56  fof(f782,plain,(
% 1.46/0.56    ~spl4_1 | ~spl4_3 | ~spl4_43 | ~spl4_14 | ~spl4_16 | spl4_44 | ~spl4_24 | ~spl4_30),
% 1.46/0.56    inference(avatar_split_clause,[],[f528,f340,f258,f779,f176,f163,f775,f106,f96])).
% 1.46/0.56  fof(f258,plain,(
% 1.46/0.56    spl4_24 <=> sK1 = k2_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.46/0.56  fof(f340,plain,(
% 1.46/0.56    spl4_30 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.46/0.56  fof(f528,plain,(
% 1.46/0.56    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl4_24 | ~spl4_30)),
% 1.46/0.56    inference(forward_demodulation,[],[f501,f260])).
% 1.46/0.56  fof(f260,plain,(
% 1.46/0.56    sK1 = k2_relat_1(sK2) | ~spl4_24),
% 1.46/0.56    inference(avatar_component_clause,[],[f258])).
% 1.46/0.56  fof(f501,plain,(
% 1.46/0.56    k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~spl4_30),
% 1.46/0.56    inference(superposition,[],[f301,f342])).
% 1.46/0.56  fof(f342,plain,(
% 1.46/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_30),
% 1.46/0.56    inference(avatar_component_clause,[],[f340])).
% 1.46/0.56  fof(f301,plain,(
% 1.46/0.56    ( ! [X14,X13] : (k5_relat_1(k2_funct_1(X13),k5_relat_1(X13,X14)) = k5_relat_1(k6_partfun1(k2_relat_1(X13)),X14) | ~v1_relat_1(X14) | ~v1_relat_1(X13) | ~v1_relat_1(k2_funct_1(X13)) | ~v2_funct_1(X13) | ~v1_funct_1(X13)) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f292])).
% 1.46/0.56  fof(f292,plain,(
% 1.46/0.56    ( ! [X14,X13] : (k5_relat_1(k2_funct_1(X13),k5_relat_1(X13,X14)) = k5_relat_1(k6_partfun1(k2_relat_1(X13)),X14) | ~v1_relat_1(X14) | ~v1_relat_1(X13) | ~v1_relat_1(k2_funct_1(X13)) | ~v2_funct_1(X13) | ~v1_funct_1(X13) | ~v1_relat_1(X13)) )),
% 1.46/0.56    inference(superposition,[],[f76,f89])).
% 1.46/0.56  fof(f89,plain,(
% 1.46/0.56    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(definition_unfolding,[],[f64,f72])).
% 1.46/0.56  fof(f64,plain,(
% 1.46/0.56    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f24])).
% 1.46/0.56  % (18676)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f23])).
% 1.46/0.56  fof(f23,plain,(
% 1.46/0.56    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f11])).
% 1.46/0.56  fof(f11,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.46/0.56  fof(f76,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f35])).
% 1.46/0.56  fof(f35,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f6])).
% 1.46/0.56  fof(f6,axiom,(
% 1.46/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.46/0.56  fof(f381,plain,(
% 1.46/0.56    ~spl4_1 | ~spl4_9 | ~spl4_2 | ~spl4_10 | spl4_30 | ~spl4_27),
% 1.46/0.56    inference(avatar_split_clause,[],[f356,f321,f340,f141,f101,f136,f96])).
% 1.46/0.56  fof(f136,plain,(
% 1.46/0.56    spl4_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.46/0.56  fof(f101,plain,(
% 1.46/0.56    spl4_2 <=> v1_funct_1(sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.46/0.56  fof(f141,plain,(
% 1.46/0.56    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.46/0.56  fof(f321,plain,(
% 1.46/0.56    spl4_27 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.46/0.56  fof(f356,plain,(
% 1.46/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_27),
% 1.46/0.56    inference(superposition,[],[f323,f75])).
% 1.46/0.56  fof(f75,plain,(
% 1.46/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f34])).
% 1.46/0.56  fof(f34,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.46/0.56    inference(flattening,[],[f33])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.46/0.56    inference(ennf_transformation,[],[f17])).
% 1.46/0.56  fof(f17,axiom,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.46/0.56  fof(f323,plain,(
% 1.46/0.56    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_27),
% 1.46/0.56    inference(avatar_component_clause,[],[f321])).
% 1.46/0.56  fof(f355,plain,(
% 1.46/0.56    ~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10 | spl4_26),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f344])).
% 1.46/0.56  fof(f344,plain,(
% 1.46/0.56    $false | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10 | spl4_26)),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f98,f103,f138,f143,f319,f74])).
% 1.46/0.56  fof(f74,plain,(
% 1.46/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.46/0.56    inference(flattening,[],[f31])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.46/0.56    inference(ennf_transformation,[],[f15])).
% 1.46/0.56  fof(f15,axiom,(
% 1.46/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.46/0.56  fof(f319,plain,(
% 1.46/0.56    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_26),
% 1.46/0.56    inference(avatar_component_clause,[],[f317])).
% 1.46/0.56  fof(f317,plain,(
% 1.46/0.56    spl4_26 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.46/0.56  fof(f143,plain,(
% 1.46/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_10),
% 1.46/0.56    inference(avatar_component_clause,[],[f141])).
% 1.46/0.56  fof(f138,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_9),
% 1.46/0.56    inference(avatar_component_clause,[],[f136])).
% 1.46/0.56  fof(f103,plain,(
% 1.46/0.56    v1_funct_1(sK3) | ~spl4_2),
% 1.46/0.56    inference(avatar_component_clause,[],[f101])).
% 1.46/0.56  fof(f324,plain,(
% 1.46/0.56    ~spl4_26 | spl4_27 | ~spl4_12),
% 1.46/0.56    inference(avatar_split_clause,[],[f314,f151,f321,f317])).
% 1.46/0.56  fof(f151,plain,(
% 1.46/0.56    spl4_12 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.46/0.56  fof(f314,plain,(
% 1.46/0.56    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_12),
% 1.46/0.56    inference(resolution,[],[f311,f153])).
% 1.46/0.56  fof(f153,plain,(
% 1.46/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_12),
% 1.46/0.56    inference(avatar_component_clause,[],[f151])).
% 1.46/0.56  fof(f311,plain,(
% 1.46/0.56    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.46/0.56    inference(resolution,[],[f68,f71])).
% 1.46/0.56  fof(f71,plain,(
% 1.46/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f16])).
% 1.46/0.56  fof(f16,axiom,(
% 1.46/0.56    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.46/0.56  fof(f68,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f49])).
% 1.46/0.56  fof(f49,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(nnf_transformation,[],[f30])).
% 1.46/0.56  fof(f30,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(flattening,[],[f29])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.46/0.56    inference(ennf_transformation,[],[f14])).
% 1.46/0.56  fof(f14,axiom,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.46/0.56  fof(f261,plain,(
% 1.46/0.56    ~spl4_9 | spl4_24 | ~spl4_11),
% 1.46/0.56    inference(avatar_split_clause,[],[f249,f146,f258,f136])).
% 1.46/0.56  fof(f146,plain,(
% 1.46/0.56    spl4_11 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.46/0.56  fof(f249,plain,(
% 1.46/0.56    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 1.46/0.56    inference(superposition,[],[f77,f148])).
% 1.46/0.56  fof(f148,plain,(
% 1.46/0.56    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_11),
% 1.46/0.56    inference(avatar_component_clause,[],[f146])).
% 1.46/0.56  fof(f77,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f36])).
% 1.46/0.56  fof(f36,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f13])).
% 1.46/0.56  fof(f13,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.46/0.56  fof(f203,plain,(
% 1.46/0.56    spl4_18 | ~spl4_10),
% 1.46/0.56    inference(avatar_split_clause,[],[f192,f141,f200])).
% 1.46/0.56  fof(f192,plain,(
% 1.46/0.56    v4_relat_1(sK3,sK1) | ~spl4_10),
% 1.46/0.56    inference(resolution,[],[f87,f143])).
% 1.46/0.56  fof(f87,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f45])).
% 1.46/0.56  fof(f45,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f12])).
% 1.46/0.56  fof(f12,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.46/0.56  fof(f198,plain,(
% 1.46/0.56    spl4_17 | ~spl4_9),
% 1.46/0.56    inference(avatar_split_clause,[],[f191,f136,f195])).
% 1.46/0.56  fof(f191,plain,(
% 1.46/0.56    v4_relat_1(sK2,sK0) | ~spl4_9),
% 1.46/0.56    inference(resolution,[],[f87,f138])).
% 1.46/0.56  fof(f183,plain,(
% 1.46/0.56    spl4_15),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f180])).
% 1.46/0.56  fof(f180,plain,(
% 1.46/0.56    $false | spl4_15),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f79,f174])).
% 1.46/0.56  fof(f174,plain,(
% 1.46/0.56    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_15),
% 1.46/0.56    inference(avatar_component_clause,[],[f172])).
% 1.46/0.56  fof(f172,plain,(
% 1.46/0.56    spl4_15 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.46/0.56  fof(f79,plain,(
% 1.46/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.46/0.56  fof(f179,plain,(
% 1.46/0.56    ~spl4_15 | spl4_16 | ~spl4_10),
% 1.46/0.56    inference(avatar_split_clause,[],[f156,f141,f176,f172])).
% 1.46/0.56  fof(f156,plain,(
% 1.46/0.56    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_10),
% 1.46/0.56    inference(resolution,[],[f78,f143])).
% 1.46/0.56  fof(f78,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f37])).
% 1.46/0.56  fof(f37,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.46/0.56  fof(f170,plain,(
% 1.46/0.56    spl4_13),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f167])).
% 1.46/0.56  fof(f167,plain,(
% 1.46/0.56    $false | spl4_13),
% 1.46/0.56    inference(unit_resulting_resolution,[],[f79,f161])).
% 1.46/0.56  fof(f161,plain,(
% 1.46/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_13),
% 1.46/0.56    inference(avatar_component_clause,[],[f159])).
% 1.46/0.56  fof(f159,plain,(
% 1.46/0.56    spl4_13 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.46/0.56  fof(f166,plain,(
% 1.46/0.56    ~spl4_13 | spl4_14 | ~spl4_9),
% 1.46/0.56    inference(avatar_split_clause,[],[f155,f136,f163,f159])).
% 1.46/0.56  fof(f155,plain,(
% 1.46/0.56    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_9),
% 1.46/0.56    inference(resolution,[],[f78,f138])).
% 1.46/0.56  fof(f154,plain,(
% 1.46/0.56    spl4_12),
% 1.46/0.56    inference(avatar_split_clause,[],[f58,f151])).
% 1.46/0.56  fof(f58,plain,(
% 1.46/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.46/0.56    inference(cnf_transformation,[],[f48])).
% 1.46/0.56  fof(f48,plain,(
% 1.46/0.56    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f47,f46])).
% 1.46/0.56  fof(f46,plain,(
% 1.46/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f47,plain,(
% 1.46/0.56    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f22,plain,(
% 1.46/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f21])).
% 1.46/0.56  fof(f21,plain,(
% 1.46/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f20])).
% 1.46/0.56  fof(f20,negated_conjecture,(
% 1.46/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.46/0.56    inference(negated_conjecture,[],[f19])).
% 1.46/0.56  fof(f19,conjecture,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.46/0.56  fof(f149,plain,(
% 1.46/0.56    spl4_11),
% 1.46/0.56    inference(avatar_split_clause,[],[f57,f146])).
% 1.46/0.56  fof(f57,plain,(
% 1.46/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f48])).
% 1.46/0.56  fof(f144,plain,(
% 1.46/0.56    spl4_10),
% 1.46/0.56    inference(avatar_split_clause,[],[f56,f141])).
% 1.46/0.56  fof(f56,plain,(
% 1.46/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.46/0.56    inference(cnf_transformation,[],[f48])).
% 1.46/0.56  fof(f139,plain,(
% 1.46/0.56    spl4_9),
% 1.46/0.56    inference(avatar_split_clause,[],[f53,f136])).
% 1.46/0.56  fof(f53,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.46/0.56    inference(cnf_transformation,[],[f48])).
% 1.46/0.56  fof(f134,plain,(
% 1.46/0.56    ~spl4_8),
% 1.46/0.56    inference(avatar_split_clause,[],[f62,f131])).
% 1.46/0.56  fof(f62,plain,(
% 1.46/0.56    k2_funct_1(sK2) != sK3),
% 1.46/0.56    inference(cnf_transformation,[],[f48])).
% 1.46/0.56  fof(f109,plain,(
% 1.46/0.56    spl4_3),
% 1.46/0.56    inference(avatar_split_clause,[],[f59,f106])).
% 1.46/0.56  fof(f59,plain,(
% 1.46/0.56    v2_funct_1(sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f48])).
% 1.46/0.56  fof(f104,plain,(
% 1.46/0.56    spl4_2),
% 1.46/0.56    inference(avatar_split_clause,[],[f54,f101])).
% 1.46/0.56  fof(f54,plain,(
% 1.46/0.56    v1_funct_1(sK3)),
% 1.46/0.56    inference(cnf_transformation,[],[f48])).
% 1.46/0.56  fof(f99,plain,(
% 1.46/0.56    spl4_1),
% 1.46/0.56    inference(avatar_split_clause,[],[f51,f96])).
% 1.46/0.56  fof(f51,plain,(
% 1.46/0.56    v1_funct_1(sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f48])).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (18674)------------------------------
% 1.46/0.56  % (18674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (18674)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (18674)Memory used [KB]: 12025
% 1.46/0.56  % (18674)Time elapsed: 0.096 s
% 1.46/0.56  % (18674)------------------------------
% 1.46/0.56  % (18674)------------------------------
% 1.46/0.56  % (18669)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.56  % (18645)Success in time 0.203 s
%------------------------------------------------------------------------------
