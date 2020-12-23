%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  98 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 221 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f53,f127,f162,f201])).

fof(f201,plain,
    ( spl2_5
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl2_5
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f197,f128])).

fof(f128,plain,
    ( k1_xboole_0 != k6_subset_1(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f126,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f126,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl2_5
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f197,plain,
    ( k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ spl2_7 ),
    inference(superposition,[],[f31,f161])).

fof(f161,plain,
    ( k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl2_7
  <=> k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f31,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f162,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f78,f43,f38,f159])).

fof(f38,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f43,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f78,plain,
    ( k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f40,f45,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f45,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f40,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f127,plain,
    ( ~ spl2_5
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f90,f50,f43,f38,f124])).

fof(f50,plain,
    ( spl2_3
  <=> r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f90,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(forward_demodulation,[],[f89,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f89,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(forward_demodulation,[],[f88,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f88,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(backward_demodulation,[],[f71,f82])).

fof(f82,plain,
    ( ! [X0] : k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f45,f47,f22])).

fof(f47,plain,
    ( ! [X0] : v1_relat_1(k6_subset_1(sK0,X0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f40,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f71,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f30,f24])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f52,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f53,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:35:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (24468)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (24461)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (24462)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (24457)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (24470)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (24455)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (24458)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (24467)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (24466)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (24463)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (24470)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f41,f46,f53,f127,f162,f201])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    spl2_5 | ~spl2_7),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f200])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    $false | (spl2_5 | ~spl2_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f197,f128])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    k1_xboole_0 != k6_subset_1(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) | spl2_5),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f126,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f28,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) | spl2_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f124])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    spl2_5 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) | ~spl2_7),
% 0.20/0.49    inference(superposition,[],[f31,f161])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f159])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    spl2_7 <=> k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f23,f24])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    spl2_7 | ~spl2_1 | ~spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f78,f43,f38,f159])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    spl2_1 <=> v1_relat_1(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    spl2_2 <=> v1_relat_1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    k1_relat_1(k2_xboole_0(sK0,sK1)) = k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | (~spl2_1 | ~spl2_2)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f45,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    v1_relat_1(sK1) | ~spl2_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f43])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    v1_relat_1(sK0) | ~spl2_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f38])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ~spl2_5 | ~spl2_1 | ~spl2_2 | spl2_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f90,f50,f43,f38,f124])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl2_3 <=> r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) | (~spl2_1 | ~spl2_2 | spl2_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f89,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,sK0))) | (~spl2_1 | ~spl2_2 | spl2_3)),
% 0.20/0.49    inference(forward_demodulation,[],[f88,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f26,f24])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) | (~spl2_1 | ~spl2_2 | spl2_3)),
% 0.20/0.49    inference(backward_demodulation,[],[f71,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0)))) ) | (~spl2_1 | ~spl2_2)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f45,f47,f22])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_subset_1(sK0,X0))) ) | ~spl2_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f27,f24])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ~r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) | spl2_3),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f52,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f30,f24])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) | spl2_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f50])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ~spl2_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f21,f50])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f20,f43])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    v1_relat_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    spl2_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f19,f38])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    v1_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (24470)------------------------------
% 0.20/0.49  % (24470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (24470)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (24470)Memory used [KB]: 10874
% 0.20/0.49  % (24470)Time elapsed: 0.013 s
% 0.20/0.49  % (24470)------------------------------
% 0.20/0.49  % (24470)------------------------------
% 0.20/0.49  % (24454)Success in time 0.127 s
%------------------------------------------------------------------------------
