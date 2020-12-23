%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 126 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :   76 ( 159 expanded)
%              Number of equality atoms :   28 (  87 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1776,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f1773,f1775])).

fof(f1775,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f1774])).

fof(f1774,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f152,f1750])).

fof(f1750,plain,(
    ! [X2,X3] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X3,X2)),k9_relat_1(sK2,X2)) ),
    inference(superposition,[],[f1683,f34])).

fof(f34,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1683,plain,(
    ! [X61,X62] : r1_tarski(k9_relat_1(sK2,X62),k9_relat_1(sK2,k2_xboole_0(X61,X62))) ),
    inference(superposition,[],[f43,f1526])).

fof(f1526,plain,(
    ! [X28,X27] : k9_relat_1(sK2,X28) = k3_xboole_0(k9_relat_1(sK2,k2_xboole_0(X27,X28)),k9_relat_1(sK2,X28)) ),
    inference(superposition,[],[f1142,f860])).

fof(f860,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(resolution,[],[f30,f19])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(f1142,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f1141,f23])).

fof(f1141,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f1140,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f1140,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f1071,f445])).

fof(f445,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X10,X8)) ),
    inference(superposition,[],[f290,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f290,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3))) = X3 ),
    inference(forward_demodulation,[],[f289,f24])).

fof(f289,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k2_xboole_0(X3,X5)) = k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3))) ),
    inference(forward_demodulation,[],[f253,f22])).

fof(f253,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3))) = k3_xboole_0(k2_xboole_0(X3,X5),X3) ),
    inference(superposition,[],[f27,f34])).

fof(f1071,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f32,f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k2_xboole_0(X2,X0),k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f29,f22])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_xboole_1)).

fof(f43,plain,(
    ! [X2,X0] : r1_tarski(k3_xboole_0(X0,X2),X0) ),
    inference(superposition,[],[f25,f23])).

fof(f25,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f152,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1773,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f1763])).

fof(f1763,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f1749,f148])).

fof(f148,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1749,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0)) ),
    inference(superposition,[],[f1683,f23])).

fof(f153,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f139,f150,f146])).

fof(f139,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (7653)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (7656)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.41  % (7652)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.44  % (7654)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.44  % (7655)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.45  % (7651)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.46  % (7657)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.47  % (7659)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.47  % (7649)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.47  % (7650)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.47  % (7648)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.48  % (7658)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.53  % (7648)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1776,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f153,f1773,f1775])).
% 0.21/0.53  fof(f1775,plain,(
% 0.21/0.53    spl3_2),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1774])).
% 0.21/0.53  fof(f1774,plain,(
% 0.21/0.53    $false | spl3_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f152,f1750])).
% 0.21/0.53  fof(f1750,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X3,X2)),k9_relat_1(sK2,X2))) )),
% 0.21/0.53    inference(superposition,[],[f1683,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1) )),
% 0.21/0.53    inference(superposition,[],[f23,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.53  fof(f1683,plain,(
% 0.21/0.53    ( ! [X61,X62] : (r1_tarski(k9_relat_1(sK2,X62),k9_relat_1(sK2,k2_xboole_0(X61,X62)))) )),
% 0.21/0.53    inference(superposition,[],[f43,f1526])).
% 0.21/0.53  fof(f1526,plain,(
% 0.21/0.53    ( ! [X28,X27] : (k9_relat_1(sK2,X28) = k3_xboole_0(k9_relat_1(sK2,k2_xboole_0(X27,X28)),k9_relat_1(sK2,X28))) )),
% 0.21/0.53    inference(superposition,[],[f1142,f860])).
% 0.21/0.53  fof(f860,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.21/0.53    inference(resolution,[],[f30,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).
% 0.21/0.53  fof(f1142,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f1141,f23])).
% 0.21/0.53  fof(f1141,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f1140,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 0.21/0.53  fof(f1140,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f1071,f445])).
% 0.21/0.53  fof(f445,plain,(
% 0.21/0.53    ( ! [X10,X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X10,X8))) )),
% 0.21/0.53    inference(superposition,[],[f290,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3))) = X3) )),
% 0.21/0.53    inference(forward_demodulation,[],[f289,f24])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k2_xboole_0(X3,X5)) = k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f253,f22])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k3_xboole_0(X5,k3_xboole_0(X4,X3))) = k3_xboole_0(k2_xboole_0(X3,X5),X3)) )),
% 0.21/0.53    inference(superposition,[],[f27,f34])).
% 0.21/0.53  fof(f1071,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(k2_xboole_0(X0,X0),k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(superposition,[],[f32,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.53    inference(rectify,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k2_xboole_0(X2,X0),k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f29,f22])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_xboole_1)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0] : (r1_tarski(k3_xboole_0(X0,X2),X0)) )),
% 0.21/0.53    inference(superposition,[],[f25,f23])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    spl3_2 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f1773,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1763])).
% 0.21/0.53  fof(f1763,plain,(
% 0.21/0.53    $false | spl3_1),
% 0.21/0.53    inference(resolution,[],[f1749,f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0)) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f146])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f1749,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X0))) )),
% 0.21/0.53    inference(superposition,[],[f1683,f23])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f139,f150,f146])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK1)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k9_relat_1(sK2,sK0))),
% 0.21/0.53    inference(resolution,[],[f31,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (7648)------------------------------
% 0.21/0.53  % (7648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7648)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (7648)Memory used [KB]: 11897
% 0.21/0.53  % (7648)Time elapsed: 0.099 s
% 0.21/0.53  % (7648)------------------------------
% 0.21/0.53  % (7648)------------------------------
% 0.21/0.53  % (7647)Success in time 0.176 s
%------------------------------------------------------------------------------
