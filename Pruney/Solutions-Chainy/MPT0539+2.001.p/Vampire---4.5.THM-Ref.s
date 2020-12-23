%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :   76 ( 132 expanded)
%              Number of equality atoms :   18 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f209,f253])).

fof(f253,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,
    ( k5_relat_1(sK1,k8_relat_1(sK0,sK2)) != k5_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ spl3_3 ),
    inference(superposition,[],[f13,f222])).

fof(f222,plain,
    ( ! [X6] : k8_relat_1(X6,k5_relat_1(sK1,sK2)) = k5_relat_1(sK1,k8_relat_1(X6,sK2))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f213,f169])).

fof(f169,plain,(
    ! [X3] : k5_relat_1(k5_relat_1(sK1,sK2),k6_relat_1(X3)) = k5_relat_1(sK1,k8_relat_1(X3,sK2)) ),
    inference(forward_demodulation,[],[f162,f22])).

fof(f22,plain,(
    ! [X6] : k8_relat_1(X6,sK2) = k5_relat_1(sK2,k6_relat_1(X6)) ),
    inference(resolution,[],[f17,f12])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(X1,k8_relat_1(X0,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f162,plain,(
    ! [X3] : k5_relat_1(k5_relat_1(sK1,sK2),k6_relat_1(X3)) = k5_relat_1(sK1,k5_relat_1(sK2,k6_relat_1(X3))) ),
    inference(resolution,[],[f73,f15])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f73,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k5_relat_1(k5_relat_1(sK1,sK2),X16) = k5_relat_1(sK1,k5_relat_1(sK2,X16)) ) ),
    inference(resolution,[],[f35,f12])).

fof(f35,plain,(
    ! [X14,X13] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | k5_relat_1(k5_relat_1(sK1,X13),X14) = k5_relat_1(sK1,k5_relat_1(X13,X14)) ) ),
    inference(resolution,[],[f16,f14])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
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
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f213,plain,
    ( ! [X6] : k8_relat_1(X6,k5_relat_1(sK1,sK2)) = k5_relat_1(k5_relat_1(sK1,sK2),k6_relat_1(X6))
    | ~ spl3_3 ),
    inference(resolution,[],[f199,f17])).

fof(f199,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl3_3
  <=> v1_relat_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f13,plain,(
    k8_relat_1(sK0,k5_relat_1(sK1,sK2)) != k5_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f209,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f207,f14])).

fof(f207,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f206,f12])).

fof(f206,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl3_3 ),
    inference(resolution,[],[f200,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f200,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (13172)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.42  % (13173)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.45  % (13175)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.45  % (13167)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.45  % (13171)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.46  % (13178)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.46  % (13167)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f254,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f209,f253])).
% 0.21/0.46  fof(f253,plain,(
% 0.21/0.46    ~spl3_3),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f252])).
% 0.21/0.46  fof(f252,plain,(
% 0.21/0.46    $false | ~spl3_3),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f251])).
% 0.21/0.46  fof(f251,plain,(
% 0.21/0.46    k5_relat_1(sK1,k8_relat_1(sK0,sK2)) != k5_relat_1(sK1,k8_relat_1(sK0,sK2)) | ~spl3_3),
% 0.21/0.46    inference(superposition,[],[f13,f222])).
% 0.21/0.46  fof(f222,plain,(
% 0.21/0.46    ( ! [X6] : (k8_relat_1(X6,k5_relat_1(sK1,sK2)) = k5_relat_1(sK1,k8_relat_1(X6,sK2))) ) | ~spl3_3),
% 0.21/0.46    inference(forward_demodulation,[],[f213,f169])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    ( ! [X3] : (k5_relat_1(k5_relat_1(sK1,sK2),k6_relat_1(X3)) = k5_relat_1(sK1,k8_relat_1(X3,sK2))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f162,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X6] : (k8_relat_1(X6,sK2) = k5_relat_1(sK2,k6_relat_1(X6))) )),
% 0.21/0.46    inference(resolution,[],[f17,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    v1_relat_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) != k5_relat_1(X1,k8_relat_1(X0,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    ( ! [X3] : (k5_relat_1(k5_relat_1(sK1,sK2),k6_relat_1(X3)) = k5_relat_1(sK1,k5_relat_1(sK2,k6_relat_1(X3)))) )),
% 0.21/0.46    inference(resolution,[],[f73,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ( ! [X16] : (~v1_relat_1(X16) | k5_relat_1(k5_relat_1(sK1,sK2),X16) = k5_relat_1(sK1,k5_relat_1(sK2,X16))) )),
% 0.21/0.46    inference(resolution,[],[f35,f12])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X14,X13] : (~v1_relat_1(X13) | ~v1_relat_1(X14) | k5_relat_1(k5_relat_1(sK1,X13),X14) = k5_relat_1(sK1,k5_relat_1(X13,X14))) )),
% 0.21/0.46    inference(resolution,[],[f16,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.46  fof(f213,plain,(
% 0.21/0.46    ( ! [X6] : (k8_relat_1(X6,k5_relat_1(sK1,sK2)) = k5_relat_1(k5_relat_1(sK1,sK2),k6_relat_1(X6))) ) | ~spl3_3),
% 0.21/0.46    inference(resolution,[],[f199,f17])).
% 0.21/0.46  fof(f199,plain,(
% 0.21/0.46    v1_relat_1(k5_relat_1(sK1,sK2)) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f198])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    spl3_3 <=> v1_relat_1(k5_relat_1(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    k8_relat_1(sK0,k5_relat_1(sK1,sK2)) != k5_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f209,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.46  fof(f208,plain,(
% 0.21/0.46    $false | spl3_3),
% 0.21/0.46    inference(subsumption_resolution,[],[f207,f14])).
% 0.21/0.46  fof(f207,plain,(
% 0.21/0.46    ~v1_relat_1(sK1) | spl3_3),
% 0.21/0.46    inference(subsumption_resolution,[],[f206,f12])).
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | spl3_3),
% 0.21/0.46    inference(resolution,[],[f200,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    ~v1_relat_1(k5_relat_1(sK1,sK2)) | spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f198])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (13167)------------------------------
% 0.21/0.46  % (13167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (13167)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (13167)Memory used [KB]: 10874
% 0.21/0.46  % (13167)Time elapsed: 0.041 s
% 0.21/0.46  % (13167)------------------------------
% 0.21/0.46  % (13167)------------------------------
% 0.21/0.46  % (13169)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.46  % (13168)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.46  % (13166)Success in time 0.099 s
%------------------------------------------------------------------------------
