%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  53 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 110 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f37,f45,f69])).

fof(f69,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl3_1
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k7_relat_1(k8_relat_1(sK0,sK2),sK1)
    | spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f20,f44])).

fof(f44,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k8_relat_1(X0,sK2),X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_4
  <=> ! [X1,X0] : k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k8_relat_1(X0,sK2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f20,plain,
    ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl3_1
  <=> k7_relat_1(k8_relat_1(sK0,sK2),sK1) = k8_relat_1(sK0,k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f45,plain,
    ( spl3_4
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f35,f23,f43])).

fof(f23,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f35,plain,
    ( spl3_3
  <=> ! [X1,X0] : k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f41,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k8_relat_1(X0,sK2),X1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f38,f25])).

fof(f25,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f38,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k8_relat_1(X0,sK2),X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_3 ),
    inference(superposition,[],[f36,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f36,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f37,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f31,f23,f35])).

fof(f31,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1)
    | ~ spl3_2 ),
    inference(resolution,[],[f30,f25])).

fof(f30,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(X3)
      | k8_relat_1(X5,k7_relat_1(X3,X4)) = k7_relat_1(k5_relat_1(X3,k6_relat_1(X5)),X4) ) ),
    inference(subsumption_resolution,[],[f29,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f29,plain,(
    ! [X4,X5,X3] :
      ( k8_relat_1(X5,k7_relat_1(X3,X4)) = k7_relat_1(k5_relat_1(X3,k6_relat_1(X5)),X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f27,f13])).

fof(f13,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f27,plain,(
    ! [X4,X5,X3] :
      ( k8_relat_1(X5,k7_relat_1(X3,X4)) = k7_relat_1(k5_relat_1(X3,k6_relat_1(X5)),X4)
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f16,f15])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f26,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f11,f23])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f21,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f18])).

fof(f12,plain,(
    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (18727)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.13/0.41  % (18720)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.42  % (18719)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  % (18719)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f21,f26,f37,f45,f69])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl3_1 | ~spl3_4),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f68])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    $false | (spl3_1 | ~spl3_4)),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f67])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k7_relat_1(k8_relat_1(sK0,sK2),sK1) | (spl3_1 | ~spl3_4)),
% 0.20/0.43    inference(superposition,[],[f20,f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k8_relat_1(X0,sK2),X1)) ) | ~spl3_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    spl3_4 <=> ! [X1,X0] : k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k8_relat_1(X0,sK2),X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) | spl3_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    spl3_1 <=> k7_relat_1(k8_relat_1(sK0,sK2),sK1) = k8_relat_1(sK0,k7_relat_1(sK2,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    spl3_4 | ~spl3_2 | ~spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f41,f35,f23,f43])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    spl3_2 <=> v1_relat_1(sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl3_3 <=> ! [X1,X0] : k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k8_relat_1(X0,sK2),X1)) ) | (~spl3_2 | ~spl3_3)),
% 0.20/0.43    inference(subsumption_resolution,[],[f38,f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    v1_relat_1(sK2) | ~spl3_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f23])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k8_relat_1(X0,sK2),X1) | ~v1_relat_1(sK2)) ) | ~spl3_3),
% 0.20/0.43    inference(superposition,[],[f36,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1)) ) | ~spl3_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f35])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    spl3_3 | ~spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f23,f35])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k8_relat_1(X0,k7_relat_1(sK2,X1)) = k7_relat_1(k5_relat_1(sK2,k6_relat_1(X0)),X1)) ) | ~spl3_2),
% 0.20/0.43    inference(resolution,[],[f30,f25])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X4,X5,X3] : (~v1_relat_1(X3) | k8_relat_1(X5,k7_relat_1(X3,X4)) = k7_relat_1(k5_relat_1(X3,k6_relat_1(X5)),X4)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f29,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X4,X5,X3] : (k8_relat_1(X5,k7_relat_1(X3,X4)) = k7_relat_1(k5_relat_1(X3,k6_relat_1(X5)),X4) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f27,f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X4,X5,X3] : (k8_relat_1(X5,k7_relat_1(X3,X4)) = k7_relat_1(k5_relat_1(X3,k6_relat_1(X5)),X4) | ~v1_relat_1(k6_relat_1(X5)) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 0.20/0.43    inference(superposition,[],[f16,f15])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f11,f23])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    v1_relat_1(sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.20/0.43    inference(negated_conjecture,[],[f5])).
% 0.20/0.43  fof(f5,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ~spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f12,f18])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (18719)------------------------------
% 0.20/0.43  % (18719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (18719)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (18719)Memory used [KB]: 10618
% 0.20/0.43  % (18719)Time elapsed: 0.005 s
% 0.20/0.43  % (18719)------------------------------
% 0.20/0.43  % (18719)------------------------------
% 0.20/0.44  % (18721)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.44  % (18717)Success in time 0.086 s
%------------------------------------------------------------------------------
