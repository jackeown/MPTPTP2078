%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 123 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 260 expanded)
%              Number of equality atoms :   13 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f212,f214,f222,f233,f235])).

fof(f235,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f215,f26])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(f215,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_6 ),
    inference(resolution,[],[f207,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f69,plain,(
    ! [X2,X3] : r1_tarski(k6_subset_1(X2,X3),X2) ),
    inference(resolution,[],[f46,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f43,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f41,f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f207,plain,
    ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl2_6
  <=> v1_relat_1(k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f233,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f221,f26])).

fof(f221,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl2_8
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f222,plain,
    ( ~ spl2_8
    | ~ spl2_5
    | spl2_7 ),
    inference(avatar_split_clause,[],[f216,f209,f201,f219])).

fof(f201,plain,
    ( spl2_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f209,plain,
    ( spl2_7
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f216,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl2_7 ),
    inference(resolution,[],[f211,f105])).

fof(f105,plain,(
    ! [X12,X11] :
      ( r1_tarski(k2_relat_1(X11),k2_relat_1(k3_tarski(k2_tarski(X11,X12))))
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X11) ) ),
    inference(superposition,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f29,f36,f36])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f211,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK0,sK1))))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f209])).

fof(f214,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f203,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f203,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f201])).

fof(f212,plain,
    ( ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f199,f209,f205,f201])).

fof(f199,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK0,sK1))))
    | ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f198,f34])).

fof(f198,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,sK0))))
    | ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f196,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f37,f36,f35,f36])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f196,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))))
    | ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f100,f28])).

fof(f28,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X2,k2_relat_1(X0)),k2_relat_1(X1))
      | ~ r1_tarski(X2,k2_relat_1(k3_tarski(k2_tarski(X0,X1))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:41:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (17245)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (17237)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (17243)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (17239)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (17247)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (17236)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (17239)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (17238)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (17244)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (17242)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (17246)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (17248)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (17252)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f212,f214,f222,f233,f235])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    spl2_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f234])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    $false | spl2_6),
% 0.21/0.49    inference(resolution,[],[f215,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f23,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | spl2_6),
% 0.21/0.49    inference(resolution,[],[f207,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f69,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f32,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r1_tarski(k6_subset_1(X2,X3),X2)) )),
% 0.21/0.49    inference(resolution,[],[f46,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 0.21/0.49    inference(superposition,[],[f43,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f33,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f41,f35,f36])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ~v1_relat_1(k6_subset_1(sK0,sK1)) | spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f205])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    spl2_6 <=> v1_relat_1(k6_subset_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    spl2_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f232])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    $false | spl2_8),
% 0.21/0.49    inference(resolution,[],[f221,f26])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | spl2_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f219])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    spl2_8 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ~spl2_8 | ~spl2_5 | spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f216,f209,f201,f219])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    spl2_5 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    spl2_7 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK0,sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl2_7),
% 0.21/0.49    inference(resolution,[],[f211,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X12,X11] : (r1_tarski(k2_relat_1(X11),k2_relat_1(k3_tarski(k2_tarski(X11,X12)))) | ~v1_relat_1(X12) | ~v1_relat_1(X11)) )),
% 0.21/0.49    inference(superposition,[],[f43,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f29,f36,f36])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK0,sK1)))) | spl2_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f209])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    spl2_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f213])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    $false | spl2_5),
% 0.21/0.49    inference(resolution,[],[f203,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f201])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    ~spl2_5 | ~spl2_6 | ~spl2_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f199,f209,f205,f201])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK0,sK1)))) | ~v1_relat_1(k6_subset_1(sK0,sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f198,f34])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,sK0)))) | ~v1_relat_1(k6_subset_1(sK0,sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f196,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f37,f36,f35,f36])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))) | ~v1_relat_1(k6_subset_1(sK0,sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f100,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X2,k2_relat_1(X0)),k2_relat_1(X1)) | ~r1_tarski(X2,k2_relat_1(k3_tarski(k2_tarski(X0,X1)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(superposition,[],[f46,f42])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17239)------------------------------
% 0.21/0.49  % (17239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17239)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17239)Memory used [KB]: 6268
% 0.21/0.49  % (17239)Time elapsed: 0.061 s
% 0.21/0.49  % (17239)------------------------------
% 0.21/0.49  % (17239)------------------------------
% 0.21/0.49  % (17249)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (17234)Success in time 0.134 s
%------------------------------------------------------------------------------
