%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:53 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 124 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :    6
%              Number of atoms          :  188 ( 297 expanded)
%              Number of equality atoms :   50 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f35,f39,f43,f47,f51,f58,f66,f73,f88,f107,f149,f166,f173,f177])).

fof(f177,plain,
    ( spl2_1
    | ~ spl2_30 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl2_1
    | ~ spl2_30 ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,
    ( k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0)
    | spl2_1
    | ~ spl2_30 ),
    inference(superposition,[],[f25,f171])).

fof(f171,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl2_30
  <=> ! [X0] : k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f25,plain,
    ( k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl2_1
  <=> k2_wellord1(sK1,sK0) = k8_relat_1(sK0,k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f173,plain,
    ( spl2_30
    | ~ spl2_11
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f168,f163,f71,f170])).

fof(f71,plain,
    ( spl2_11
  <=> ! [X0] : k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f163,plain,
    ( spl2_29
  <=> ! [X3,X2] : k7_relat_1(k8_relat_1(X3,sK1),X2) = k8_relat_1(X3,k7_relat_1(sK1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f168,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0))
    | ~ spl2_11
    | ~ spl2_29 ),
    inference(superposition,[],[f72,f164])).

fof(f164,plain,
    ( ! [X2,X3] : k7_relat_1(k8_relat_1(X3,sK1),X2) = k8_relat_1(X3,k7_relat_1(sK1,X2))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f163])).

fof(f72,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f166,plain,
    ( spl2_29
    | ~ spl2_14
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f161,f147,f86,f163])).

fof(f86,plain,
    ( spl2_14
  <=> ! [X1,X0] : k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f147,plain,
    ( spl2_26
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) = k8_relat_1(X0,k7_relat_1(sK1,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f161,plain,
    ( ! [X0,X1] : k7_relat_1(k8_relat_1(X1,sK1),X0) = k8_relat_1(X1,k7_relat_1(sK1,X0))
    | ~ spl2_14
    | ~ spl2_26 ),
    inference(superposition,[],[f87,f148])).

fof(f148,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) = k8_relat_1(X0,k7_relat_1(sK1,X1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f147])).

fof(f87,plain,
    ( ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f86])).

fof(f149,plain,
    ( spl2_26
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f145,f105,f56,f28,f147])).

fof(f28,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f56,plain,
    ( spl2_8
  <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f105,plain,
    ( spl2_18
  <=> ! [X3,X2,X4] :
        ( ~ v1_relat_1(X2)
        | k8_relat_1(X3,k5_relat_1(k6_relat_1(X4),X2)) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X3,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f145,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) = k8_relat_1(X0,k7_relat_1(sK1,X1))
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f142,f57])).

fof(f57,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f142,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) = k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),sK1))
    | ~ spl2_2
    | ~ spl2_18 ),
    inference(resolution,[],[f106,f30])).

fof(f30,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f106,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | k8_relat_1(X3,k5_relat_1(k6_relat_1(X4),X2)) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X3,X2)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f98,f49,f33,f105])).

fof(f33,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f49,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f98,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_relat_1(X2)
        | k8_relat_1(X3,k5_relat_1(k6_relat_1(X4),X2)) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X3,X2)) )
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f50,f34])).

fof(f34,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f50,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f88,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f82,f64,f28,f86])).

fof(f64,plain,
    ( spl2_10
  <=> ! [X3,X5,X4] :
        ( k7_relat_1(k8_relat_1(X3,X4),X5) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X3,X4))
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f82,plain,
    ( ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(resolution,[],[f65,f30])).

fof(f65,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(X4)
        | k7_relat_1(k8_relat_1(X3,X4),X5) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X3,X4)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f64])).

fof(f73,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f67,f45,f28,f71])).

fof(f45,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f67,plain,
    ( ! [X0] : k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f66,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f54,f41,f37,f64])).

fof(f37,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f41,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f54,plain,
    ( ! [X4,X5,X3] :
        ( k7_relat_1(k8_relat_1(X3,X4),X5) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X3,X4))
        | ~ v1_relat_1(X4) )
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f58,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f52,f41,f28,f56])).

fof(f52,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(resolution,[],[f42,f30])).

fof(f51,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f47,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

fof(f43,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f39,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f35,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f31,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0))
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f26,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f23])).

fof(f16,plain,(
    k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:44:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.42  % (26791)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.43  % (26789)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.19/0.43  % (26791)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f178,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(avatar_sat_refutation,[],[f26,f31,f35,f39,f43,f47,f51,f58,f66,f73,f88,f107,f149,f166,f173,f177])).
% 0.19/0.43  fof(f177,plain,(
% 0.19/0.43    spl2_1 | ~spl2_30),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f176])).
% 0.19/0.43  fof(f176,plain,(
% 0.19/0.43    $false | (spl2_1 | ~spl2_30)),
% 0.19/0.43    inference(trivial_inequality_removal,[],[f175])).
% 0.19/0.43  fof(f175,plain,(
% 0.19/0.43    k2_wellord1(sK1,sK0) != k2_wellord1(sK1,sK0) | (spl2_1 | ~spl2_30)),
% 0.19/0.43    inference(superposition,[],[f25,f171])).
% 0.19/0.43  fof(f171,plain,(
% 0.19/0.43    ( ! [X0] : (k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0))) ) | ~spl2_30),
% 0.19/0.43    inference(avatar_component_clause,[],[f170])).
% 0.19/0.43  fof(f170,plain,(
% 0.19/0.43    spl2_30 <=> ! [X0] : k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.19/0.43  fof(f25,plain,(
% 0.19/0.43    k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0)) | spl2_1),
% 0.19/0.43    inference(avatar_component_clause,[],[f23])).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    spl2_1 <=> k2_wellord1(sK1,sK0) = k8_relat_1(sK0,k7_relat_1(sK1,sK0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.43  fof(f173,plain,(
% 0.19/0.43    spl2_30 | ~spl2_11 | ~spl2_29),
% 0.19/0.43    inference(avatar_split_clause,[],[f168,f163,f71,f170])).
% 0.19/0.43  fof(f71,plain,(
% 0.19/0.43    spl2_11 <=> ! [X0] : k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.19/0.43  fof(f163,plain,(
% 0.19/0.43    spl2_29 <=> ! [X3,X2] : k7_relat_1(k8_relat_1(X3,sK1),X2) = k8_relat_1(X3,k7_relat_1(sK1,X2))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.19/0.43  fof(f168,plain,(
% 0.19/0.43    ( ! [X0] : (k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0))) ) | (~spl2_11 | ~spl2_29)),
% 0.19/0.43    inference(superposition,[],[f72,f164])).
% 0.19/0.43  fof(f164,plain,(
% 0.19/0.43    ( ! [X2,X3] : (k7_relat_1(k8_relat_1(X3,sK1),X2) = k8_relat_1(X3,k7_relat_1(sK1,X2))) ) | ~spl2_29),
% 0.19/0.43    inference(avatar_component_clause,[],[f163])).
% 0.19/0.43  fof(f72,plain,(
% 0.19/0.43    ( ! [X0] : (k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0)) ) | ~spl2_11),
% 0.19/0.43    inference(avatar_component_clause,[],[f71])).
% 0.19/0.43  fof(f166,plain,(
% 0.19/0.43    spl2_29 | ~spl2_14 | ~spl2_26),
% 0.19/0.43    inference(avatar_split_clause,[],[f161,f147,f86,f163])).
% 0.19/0.43  fof(f86,plain,(
% 0.19/0.43    spl2_14 <=> ! [X1,X0] : k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.19/0.43  fof(f147,plain,(
% 0.19/0.43    spl2_26 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) = k8_relat_1(X0,k7_relat_1(sK1,X1))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.19/0.43  fof(f161,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X1,sK1),X0) = k8_relat_1(X1,k7_relat_1(sK1,X0))) ) | (~spl2_14 | ~spl2_26)),
% 0.19/0.43    inference(superposition,[],[f87,f148])).
% 0.19/0.43  fof(f148,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) = k8_relat_1(X0,k7_relat_1(sK1,X1))) ) | ~spl2_26),
% 0.19/0.43    inference(avatar_component_clause,[],[f147])).
% 0.19/0.43  fof(f87,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1))) ) | ~spl2_14),
% 0.19/0.43    inference(avatar_component_clause,[],[f86])).
% 0.19/0.43  fof(f149,plain,(
% 0.19/0.43    spl2_26 | ~spl2_2 | ~spl2_8 | ~spl2_18),
% 0.19/0.43    inference(avatar_split_clause,[],[f145,f105,f56,f28,f147])).
% 0.19/0.43  fof(f28,plain,(
% 0.19/0.43    spl2_2 <=> v1_relat_1(sK1)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.43  fof(f56,plain,(
% 0.19/0.43    spl2_8 <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.43  fof(f105,plain,(
% 0.19/0.43    spl2_18 <=> ! [X3,X2,X4] : (~v1_relat_1(X2) | k8_relat_1(X3,k5_relat_1(k6_relat_1(X4),X2)) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X3,X2)))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.19/0.43  fof(f145,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) = k8_relat_1(X0,k7_relat_1(sK1,X1))) ) | (~spl2_2 | ~spl2_8 | ~spl2_18)),
% 0.19/0.43    inference(forward_demodulation,[],[f142,f57])).
% 0.19/0.43  fof(f57,plain,(
% 0.19/0.43    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl2_8),
% 0.19/0.43    inference(avatar_component_clause,[],[f56])).
% 0.19/0.43  fof(f142,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1)) = k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),sK1))) ) | (~spl2_2 | ~spl2_18)),
% 0.19/0.43    inference(resolution,[],[f106,f30])).
% 0.19/0.43  fof(f30,plain,(
% 0.19/0.43    v1_relat_1(sK1) | ~spl2_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f28])).
% 0.19/0.43  fof(f106,plain,(
% 0.19/0.43    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k8_relat_1(X3,k5_relat_1(k6_relat_1(X4),X2)) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X3,X2))) ) | ~spl2_18),
% 0.19/0.43    inference(avatar_component_clause,[],[f105])).
% 0.19/0.43  fof(f107,plain,(
% 0.19/0.43    spl2_18 | ~spl2_3 | ~spl2_7),
% 0.19/0.43    inference(avatar_split_clause,[],[f98,f49,f33,f105])).
% 0.19/0.43  fof(f33,plain,(
% 0.19/0.43    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.43  fof(f49,plain,(
% 0.19/0.43    spl2_7 <=> ! [X1,X0,X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.43  fof(f98,plain,(
% 0.19/0.43    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k8_relat_1(X3,k5_relat_1(k6_relat_1(X4),X2)) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X3,X2))) ) | (~spl2_3 | ~spl2_7)),
% 0.19/0.43    inference(resolution,[],[f50,f34])).
% 0.19/0.43  fof(f34,plain,(
% 0.19/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.19/0.43    inference(avatar_component_clause,[],[f33])).
% 0.19/0.43  fof(f50,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))) ) | ~spl2_7),
% 0.19/0.43    inference(avatar_component_clause,[],[f49])).
% 0.19/0.43  fof(f88,plain,(
% 0.19/0.43    spl2_14 | ~spl2_2 | ~spl2_10),
% 0.19/0.43    inference(avatar_split_clause,[],[f82,f64,f28,f86])).
% 0.19/0.43  fof(f64,plain,(
% 0.19/0.43    spl2_10 <=> ! [X3,X5,X4] : (k7_relat_1(k8_relat_1(X3,X4),X5) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X3,X4)) | ~v1_relat_1(X4))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.19/0.43  fof(f82,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,sK1),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK1))) ) | (~spl2_2 | ~spl2_10)),
% 0.19/0.43    inference(resolution,[],[f65,f30])).
% 0.19/0.43  fof(f65,plain,(
% 0.19/0.43    ( ! [X4,X5,X3] : (~v1_relat_1(X4) | k7_relat_1(k8_relat_1(X3,X4),X5) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X3,X4))) ) | ~spl2_10),
% 0.19/0.43    inference(avatar_component_clause,[],[f64])).
% 0.19/0.43  fof(f73,plain,(
% 0.19/0.43    spl2_11 | ~spl2_2 | ~spl2_6),
% 0.19/0.43    inference(avatar_split_clause,[],[f67,f45,f28,f71])).
% 0.19/0.43  fof(f45,plain,(
% 0.19/0.43    spl2_6 <=> ! [X1,X0] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.19/0.43  fof(f67,plain,(
% 0.19/0.43    ( ! [X0] : (k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0)) ) | (~spl2_2 | ~spl2_6)),
% 0.19/0.43    inference(resolution,[],[f46,f30])).
% 0.19/0.43  fof(f46,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)) ) | ~spl2_6),
% 0.19/0.43    inference(avatar_component_clause,[],[f45])).
% 0.19/0.43  fof(f66,plain,(
% 0.19/0.43    spl2_10 | ~spl2_4 | ~spl2_5),
% 0.19/0.43    inference(avatar_split_clause,[],[f54,f41,f37,f64])).
% 0.19/0.43  fof(f37,plain,(
% 0.19/0.43    spl2_4 <=> ! [X1,X0] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.43  fof(f41,plain,(
% 0.19/0.43    spl2_5 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.43  fof(f54,plain,(
% 0.19/0.43    ( ! [X4,X5,X3] : (k7_relat_1(k8_relat_1(X3,X4),X5) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X3,X4)) | ~v1_relat_1(X4)) ) | (~spl2_4 | ~spl2_5)),
% 0.19/0.43    inference(resolution,[],[f42,f38])).
% 0.19/0.43  fof(f38,plain,(
% 0.19/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | ~spl2_4),
% 0.19/0.43    inference(avatar_component_clause,[],[f37])).
% 0.19/0.43  fof(f42,plain,(
% 0.19/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_5),
% 0.19/0.43    inference(avatar_component_clause,[],[f41])).
% 0.19/0.43  fof(f58,plain,(
% 0.19/0.43    spl2_8 | ~spl2_2 | ~spl2_5),
% 0.19/0.43    inference(avatar_split_clause,[],[f52,f41,f28,f56])).
% 0.19/0.43  fof(f52,plain,(
% 0.19/0.43    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | (~spl2_2 | ~spl2_5)),
% 0.19/0.43    inference(resolution,[],[f42,f30])).
% 0.19/0.43  fof(f51,plain,(
% 0.19/0.43    spl2_7),
% 0.19/0.43    inference(avatar_split_clause,[],[f21,f49])).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f12])).
% 0.19/0.43  fof(f12,plain,(
% 0.19/0.43    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.19/0.43  fof(f47,plain,(
% 0.19/0.43    spl2_6),
% 0.19/0.43    inference(avatar_split_clause,[],[f20,f45])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f11])).
% 0.19/0.43  fof(f11,plain,(
% 0.19/0.43    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f5])).
% 0.19/0.43  fof(f5,axiom,(
% 0.19/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).
% 0.19/0.43  fof(f43,plain,(
% 0.19/0.43    spl2_5),
% 0.19/0.43    inference(avatar_split_clause,[],[f19,f41])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f10])).
% 0.19/0.43  fof(f10,plain,(
% 0.19/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.19/0.43  fof(f39,plain,(
% 0.19/0.43    spl2_4),
% 0.19/0.43    inference(avatar_split_clause,[],[f18,f37])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,plain,(
% 0.19/0.43    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.19/0.43  fof(f35,plain,(
% 0.19/0.43    spl2_3),
% 0.19/0.43    inference(avatar_split_clause,[],[f17,f33])).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.19/0.43  fof(f31,plain,(
% 0.19/0.43    spl2_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f15,f28])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    v1_relat_1(sK1)),
% 0.19/0.43    inference(cnf_transformation,[],[f14])).
% 0.19/0.43  fof(f14,plain,(
% 0.19/0.43    k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).
% 0.19/0.43  fof(f13,plain,(
% 0.19/0.43    ? [X0,X1] : (k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0)) & v1_relat_1(X1)) => (k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f8,plain,(
% 0.19/0.43    ? [X0,X1] : (k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.19/0.43    inference(ennf_transformation,[],[f7])).
% 0.19/0.43  fof(f7,negated_conjecture,(
% 0.19/0.43    ~! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 0.19/0.43    inference(negated_conjecture,[],[f6])).
% 0.19/0.43  fof(f6,conjecture,(
% 0.19/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 0.19/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).
% 0.19/0.43  fof(f26,plain,(
% 0.19/0.43    ~spl2_1),
% 0.19/0.43    inference(avatar_split_clause,[],[f16,f23])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))),
% 0.19/0.43    inference(cnf_transformation,[],[f14])).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (26791)------------------------------
% 0.19/0.43  % (26791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (26791)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (26791)Memory used [KB]: 10618
% 0.19/0.43  % (26791)Time elapsed: 0.008 s
% 0.19/0.43  % (26791)------------------------------
% 0.19/0.43  % (26791)------------------------------
% 0.19/0.43  % (26784)Success in time 0.078 s
%------------------------------------------------------------------------------
