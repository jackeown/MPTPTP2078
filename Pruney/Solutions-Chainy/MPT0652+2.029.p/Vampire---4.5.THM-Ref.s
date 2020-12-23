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
% DateTime   : Thu Dec  3 12:52:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 166 expanded)
%              Number of leaves         :   23 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  274 ( 496 expanded)
%              Number of equality atoms :   83 ( 148 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f75,f100,f108,f135,f149,f161,f252,f346])).

fof(f346,plain,
    ( spl1_1
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_12
    | ~ spl1_15 ),
    inference(avatar_split_clause,[],[f345,f151,f131,f72,f66,f47])).

fof(f47,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f66,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f72,plain,
    ( spl1_6
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f131,plain,
    ( spl1_12
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f151,plain,
    ( spl1_15
  <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f345,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_12
    | ~ spl1_15 ),
    inference(forward_demodulation,[],[f344,f133])).

fof(f133,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f344,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_15 ),
    inference(forward_demodulation,[],[f286,f153])).

fof(f153,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f286,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f74,f68,f45,f41,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f68,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f74,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f252,plain,
    ( spl1_2
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_9
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f251,f145,f97,f72,f66,f51])).

fof(f51,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f97,plain,
    ( spl1_9
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f145,plain,
    ( spl1_14
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f251,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_9
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f250,f99])).

fof(f99,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f97])).

fof(f250,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_14 ),
    inference(forward_demodulation,[],[f249,f147])).

fof(f147,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f249,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f248,f114])).

fof(f114,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f68,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f248,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k7_relat_1(sK0,k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f180,f118])).

fof(f118,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f68,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f180,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))),sK0))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f68,f74,f45,f42,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(X0) != k2_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f161,plain,
    ( spl1_15
    | ~ spl1_10
    | ~ spl1_14 ),
    inference(avatar_split_clause,[],[f159,f145,f105,f151])).

fof(f105,plain,
    ( spl1_10
  <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f159,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl1_10
    | ~ spl1_14 ),
    inference(backward_demodulation,[],[f107,f147])).

fof(f107,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f149,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_14
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f143,f56,f145,f61,f66])).

fof(f61,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f56,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f143,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f36,f58])).

fof(f58,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (28393)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% (28409)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% (28414)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% (28413)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f135,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_12
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f129,f56,f131,f61,f66])).

fof(f129,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f35,f58])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f108,plain,
    ( spl1_10
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f103,f72,f105])).

fof(f103,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f74,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f100,plain,
    ( spl1_9
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f91,f66,f97])).

fof(f91,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f75,plain,
    ( spl1_6
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f70,f66,f61,f72])).

fof(f70,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f68,f63,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f63,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f69,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f64,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f31,f56])).

fof(f31,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f32,f51,f47])).

fof(f32,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:53:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (28397)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.48  % (28410)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.49  % (28396)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (28404)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (28392)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (28398)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (28398)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f75,f100,f108,f135,f149,f161,f252,f346])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    spl1_1 | ~spl1_5 | ~spl1_6 | ~spl1_12 | ~spl1_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f345,f151,f131,f72,f66,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl1_5 <=> v1_relat_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl1_6 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl1_12 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl1_15 <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.21/0.51  fof(f345,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_12 | ~spl1_15)),
% 0.21/0.51    inference(forward_demodulation,[],[f344,f133])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_15)),
% 0.21/0.51    inference(forward_demodulation,[],[f286,f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~spl1_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f151])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))) | (~spl1_5 | ~spl1_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f74,f68,f45,f41,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k1_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t198_relat_1)).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    v1_relat_1(sK0) | ~spl1_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f66])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f72])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    spl1_2 | ~spl1_5 | ~spl1_6 | ~spl1_9 | ~spl1_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f251,f145,f97,f72,f66,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl1_9 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl1_14 <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_9 | ~spl1_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f250,f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k9_relat_1(sK0,k1_relat_1(sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f249,f147])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~spl1_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0))) | (~spl1_5 | ~spl1_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f248,f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | ~spl1_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f68,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k7_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))) | (~spl1_5 | ~spl1_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f180,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) ) | ~spl1_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f68,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))),sK0)) | (~spl1_5 | ~spl1_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f68,f74,f45,f42,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_relat_1(X0) != k2_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl1_15 | ~spl1_10 | ~spl1_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f159,f145,f105,f151])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl1_10 <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | (~spl1_10 | ~spl1_14)),
% 0.21/0.51    inference(backward_demodulation,[],[f107,f147])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl1_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    ~spl1_5 | ~spl1_4 | spl1_14 | ~spl1_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f143,f56,f145,f61,f66])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl1_4 <=> v1_funct_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl1_3 <=> v2_funct_1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.21/0.51    inference(resolution,[],[f36,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    v2_funct_1(sK0) | ~spl1_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f56])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  % (28393)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (28409)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (28414)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (28413)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ~spl1_5 | ~spl1_4 | spl1_12 | ~spl1_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f129,f56,f131,f61,f66])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.21/0.51    inference(resolution,[],[f35,f58])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl1_10 | ~spl1_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f103,f72,f105])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl1_6),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f74,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl1_9 | ~spl1_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f91,f66,f97])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f68,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl1_6 | ~spl1_4 | ~spl1_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f70,f66,f61,f72])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK0)) | (~spl1_4 | ~spl1_5)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f68,f63,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    v1_funct_1(sK0) | ~spl1_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl1_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f66])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl1_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f61])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl1_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f56])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v2_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ~spl1_1 | ~spl1_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f51,f47])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (28398)------------------------------
% 0.21/0.51  % (28398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28398)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (28398)Memory used [KB]: 10874
% 0.21/0.51  % (28398)Time elapsed: 0.093 s
% 0.21/0.51  % (28398)------------------------------
% 0.21/0.51  % (28398)------------------------------
% 0.21/0.51  % (28415)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (28406)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (28391)Success in time 0.147 s
%------------------------------------------------------------------------------
