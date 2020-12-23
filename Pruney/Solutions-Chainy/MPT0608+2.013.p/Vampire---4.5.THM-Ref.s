%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  58 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 103 expanded)
%              Number of equality atoms :   36 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f90])).

fof(f90,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f35,f72])).

fof(f72,plain,
    ( ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0)))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f53,f55])).

fof(f55,plain,
    ( ! [X0] : k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f40,f43,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

fof(f43,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f42,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f28,f29])).

fof(f29,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f22,f21,f21])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f40,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f53,plain,
    ( ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f40,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

fof(f35,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_1
  <=> k6_subset_1(k1_relat_1(sK1),sK0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f33])).

fof(f18,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:30:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.38  ipcrm: permission denied for id (1234862081)
% 0.14/0.38  ipcrm: permission denied for id (1234894850)
% 0.14/0.39  ipcrm: permission denied for id (1234960388)
% 0.14/0.39  ipcrm: permission denied for id (1234993157)
% 0.14/0.39  ipcrm: permission denied for id (1235025926)
% 0.14/0.39  ipcrm: permission denied for id (1235058695)
% 0.14/0.39  ipcrm: permission denied for id (1235124232)
% 0.14/0.40  ipcrm: permission denied for id (1238368265)
% 0.14/0.40  ipcrm: permission denied for id (1238433803)
% 0.14/0.40  ipcrm: permission denied for id (1238564879)
% 0.14/0.40  ipcrm: permission denied for id (1235353616)
% 0.21/0.41  ipcrm: permission denied for id (1238663186)
% 0.21/0.41  ipcrm: permission denied for id (1238728724)
% 0.21/0.41  ipcrm: permission denied for id (1238794262)
% 0.21/0.41  ipcrm: permission denied for id (1238827031)
% 0.21/0.42  ipcrm: permission denied for id (1235550237)
% 0.21/0.42  ipcrm: permission denied for id (1235615775)
% 0.21/0.42  ipcrm: permission denied for id (1235681314)
% 0.21/0.42  ipcrm: permission denied for id (1235714083)
% 0.21/0.42  ipcrm: permission denied for id (1239121956)
% 0.21/0.42  ipcrm: permission denied for id (1239154725)
% 0.21/0.43  ipcrm: permission denied for id (1239187494)
% 0.21/0.43  ipcrm: permission denied for id (1235845160)
% 0.21/0.43  ipcrm: permission denied for id (1235877929)
% 0.21/0.43  ipcrm: permission denied for id (1235910698)
% 0.21/0.43  ipcrm: permission denied for id (1239285804)
% 0.21/0.43  ipcrm: permission denied for id (1236009005)
% 0.21/0.43  ipcrm: permission denied for id (1239318574)
% 0.21/0.43  ipcrm: permission denied for id (1239384111)
% 0.21/0.43  ipcrm: permission denied for id (1239416880)
% 0.21/0.43  ipcrm: permission denied for id (1239449649)
% 0.21/0.44  ipcrm: permission denied for id (1236140082)
% 0.21/0.44  ipcrm: permission denied for id (1236172851)
% 0.21/0.44  ipcrm: permission denied for id (1239482420)
% 0.21/0.44  ipcrm: permission denied for id (1239580727)
% 0.21/0.44  ipcrm: permission denied for id (1239646264)
% 0.21/0.44  ipcrm: permission denied for id (1239679033)
% 0.21/0.44  ipcrm: permission denied for id (1239711802)
% 0.21/0.44  ipcrm: permission denied for id (1239744571)
% 0.21/0.44  ipcrm: permission denied for id (1236336700)
% 0.21/0.45  ipcrm: permission denied for id (1239777341)
% 0.21/0.45  ipcrm: permission denied for id (1236435007)
% 0.21/0.45  ipcrm: permission denied for id (1236500545)
% 0.21/0.45  ipcrm: permission denied for id (1236533314)
% 0.21/0.45  ipcrm: permission denied for id (1236566083)
% 0.21/0.45  ipcrm: permission denied for id (1236598852)
% 0.21/0.45  ipcrm: permission denied for id (1239875653)
% 0.21/0.45  ipcrm: permission denied for id (1239908422)
% 0.21/0.45  ipcrm: permission denied for id (1239941191)
% 0.21/0.46  ipcrm: permission denied for id (1236762696)
% 0.21/0.46  ipcrm: permission denied for id (1239973961)
% 0.21/0.46  ipcrm: permission denied for id (1240006730)
% 0.21/0.46  ipcrm: permission denied for id (1240072268)
% 0.21/0.46  ipcrm: permission denied for id (1240105037)
% 0.21/0.46  ipcrm: permission denied for id (1240137806)
% 0.21/0.46  ipcrm: permission denied for id (1240170575)
% 0.21/0.46  ipcrm: permission denied for id (1236992080)
% 0.21/0.46  ipcrm: permission denied for id (1240236113)
% 0.21/0.46  ipcrm: permission denied for id (1237057618)
% 0.21/0.47  ipcrm: permission denied for id (1240334421)
% 0.21/0.47  ipcrm: permission denied for id (1237221464)
% 0.21/0.47  ipcrm: permission denied for id (1237254233)
% 0.21/0.47  ipcrm: permission denied for id (1240432730)
% 0.21/0.47  ipcrm: permission denied for id (1240498268)
% 0.21/0.47  ipcrm: permission denied for id (1237418078)
% 0.21/0.47  ipcrm: permission denied for id (1237450847)
% 0.21/0.48  ipcrm: permission denied for id (1240629346)
% 0.21/0.48  ipcrm: permission denied for id (1240662115)
% 0.21/0.48  ipcrm: permission denied for id (1237581924)
% 0.21/0.48  ipcrm: permission denied for id (1240694885)
% 0.21/0.48  ipcrm: permission denied for id (1237614695)
% 0.21/0.48  ipcrm: permission denied for id (1237647464)
% 0.21/0.49  ipcrm: permission denied for id (1240825963)
% 0.21/0.49  ipcrm: permission denied for id (1240858732)
% 0.21/0.49  ipcrm: permission denied for id (1240891501)
% 0.21/0.49  ipcrm: permission denied for id (1237844078)
% 0.21/0.49  ipcrm: permission denied for id (1240957040)
% 0.21/0.49  ipcrm: permission denied for id (1240989809)
% 0.21/0.50  ipcrm: permission denied for id (1241022578)
% 0.21/0.50  ipcrm: permission denied for id (1241055347)
% 0.21/0.50  ipcrm: permission denied for id (1237975156)
% 0.21/0.50  ipcrm: permission denied for id (1238007925)
% 0.21/0.50  ipcrm: permission denied for id (1238040695)
% 0.21/0.50  ipcrm: permission denied for id (1238073465)
% 0.21/0.50  ipcrm: permission denied for id (1241153658)
% 0.21/0.51  ipcrm: permission denied for id (1238171772)
% 0.21/0.51  ipcrm: permission denied for id (1241219197)
% 0.21/0.51  ipcrm: permission denied for id (1241251966)
% 0.21/0.51  ipcrm: permission denied for id (1238270079)
% 0.21/0.55  % (24604)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (24604)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f36,f41,f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    spl2_1 | ~spl2_2),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f35,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0)))) ) | ~spl2_2),
% 0.21/0.55    inference(backward_demodulation,[],[f53,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0] : (k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0))) ) | ~spl2_2),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f40,f43,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(flattening,[],[f12])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f42,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f24,f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f28,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f20,f21])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f19,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f22,f21,f21])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)))) ) | ~spl2_2),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f40,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) | spl2_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    spl2_1 <=> k6_subset_1(k1_relat_1(sK1),sK0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    spl2_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f17,f38])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    v1_relat_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 0.21/0.55    inference(negated_conjecture,[],[f8])).
% 0.21/0.55  fof(f8,conjecture,(
% 0.21/0.55    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ~spl2_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f18,f33])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (24604)------------------------------
% 0.21/0.55  % (24604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24604)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (24604)Memory used [KB]: 6140
% 0.21/0.55  % (24604)Time elapsed: 0.004 s
% 0.21/0.55  % (24604)------------------------------
% 0.21/0.55  % (24604)------------------------------
% 0.21/0.55  % (24443)Success in time 0.178 s
%------------------------------------------------------------------------------
