%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:06 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   62 (  80 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  103 ( 128 expanded)
%              Number of equality atoms :   45 (  61 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f53,f58,f64,f69,f86])).

fof(f86,plain,
    ( ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5
    | ~ spl0_6 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5
    | ~ spl0_6 ),
    inference(global_subsumption,[],[f18,f84])).

fof(f84,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5
    | ~ spl0_6 ),
    inference(forward_demodulation,[],[f83,f23])).

fof(f23,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f83,plain,
    ( k3_relat_1(k1_xboole_0) = k3_tarski(k1_zfmisc_1(k1_xboole_0))
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5
    | ~ spl0_6 ),
    inference(forward_demodulation,[],[f82,f68])).

fof(f68,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl0_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl0_6
  <=> k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_6])])).

fof(f82,plain,
    ( k3_relat_1(k1_xboole_0) = k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5 ),
    inference(forward_demodulation,[],[f81,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl0_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl0_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).

fof(f81,plain,
    ( k3_relat_1(k1_xboole_0) = k3_tarski(k4_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl0_4
    | ~ spl0_5 ),
    inference(forward_demodulation,[],[f72,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl0_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl0_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_4])])).

fof(f72,plain,
    ( k3_relat_1(k1_xboole_0) = k3_tarski(k4_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))
    | ~ spl0_5 ),
    inference(resolution,[],[f38,f63])).

fof(f63,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl0_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl0_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_5])])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f18,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f14])).

fof(f14,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

fof(f69,plain,(
    spl0_6 ),
    inference(avatar_split_clause,[],[f37,f66])).

fof(f37,plain,(
    k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f20,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f34])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f64,plain,
    ( spl0_5
    | ~ spl0_1 ),
    inference(avatar_split_clause,[],[f59,f40,f61])).

fof(f40,plain,
    ( spl0_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).

fof(f59,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl0_1 ),
    inference(unit_resulting_resolution,[],[f42,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f42,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl0_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f58,plain,(
    spl0_4 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f53,plain,(
    spl0_3 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    spl0_1 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (797114369)
% 0.14/0.37  ipcrm: permission denied for id (797212674)
% 0.14/0.37  ipcrm: permission denied for id (801472516)
% 0.14/0.38  ipcrm: permission denied for id (797310981)
% 0.14/0.38  ipcrm: permission denied for id (801538055)
% 0.14/0.38  ipcrm: permission denied for id (797409288)
% 0.14/0.38  ipcrm: permission denied for id (797474826)
% 0.14/0.38  ipcrm: permission denied for id (797540364)
% 0.14/0.39  ipcrm: permission denied for id (797573133)
% 0.14/0.39  ipcrm: permission denied for id (797605902)
% 0.14/0.39  ipcrm: permission denied for id (797704209)
% 0.14/0.39  ipcrm: permission denied for id (797736978)
% 0.14/0.40  ipcrm: permission denied for id (801767445)
% 0.14/0.40  ipcrm: permission denied for id (801800214)
% 0.14/0.40  ipcrm: permission denied for id (801832983)
% 0.14/0.40  ipcrm: permission denied for id (797933592)
% 0.14/0.40  ipcrm: permission denied for id (801865753)
% 0.14/0.40  ipcrm: permission denied for id (801898522)
% 0.14/0.40  ipcrm: permission denied for id (798064667)
% 0.14/0.40  ipcrm: permission denied for id (801931292)
% 0.14/0.41  ipcrm: permission denied for id (798162974)
% 0.14/0.41  ipcrm: permission denied for id (798195743)
% 0.14/0.41  ipcrm: permission denied for id (802029601)
% 0.14/0.41  ipcrm: permission denied for id (798294050)
% 0.14/0.42  ipcrm: permission denied for id (798359588)
% 0.14/0.42  ipcrm: permission denied for id (798392357)
% 0.14/0.42  ipcrm: permission denied for id (802095142)
% 0.14/0.42  ipcrm: permission denied for id (802127911)
% 0.21/0.42  ipcrm: permission denied for id (798523433)
% 0.21/0.42  ipcrm: permission denied for id (802226219)
% 0.21/0.43  ipcrm: permission denied for id (798621740)
% 0.21/0.43  ipcrm: permission denied for id (798654509)
% 0.21/0.43  ipcrm: permission denied for id (802258990)
% 0.21/0.43  ipcrm: permission denied for id (798720047)
% 0.21/0.43  ipcrm: permission denied for id (802291760)
% 0.21/0.43  ipcrm: permission denied for id (798785585)
% 0.21/0.43  ipcrm: permission denied for id (798818354)
% 0.21/0.43  ipcrm: permission denied for id (798851123)
% 0.21/0.44  ipcrm: permission denied for id (798883892)
% 0.21/0.44  ipcrm: permission denied for id (802324533)
% 0.21/0.44  ipcrm: permission denied for id (798949430)
% 0.21/0.44  ipcrm: permission denied for id (802357303)
% 0.21/0.44  ipcrm: permission denied for id (799014968)
% 0.21/0.44  ipcrm: permission denied for id (802390073)
% 0.21/0.44  ipcrm: permission denied for id (799080506)
% 0.21/0.45  ipcrm: permission denied for id (799113275)
% 0.21/0.45  ipcrm: permission denied for id (799146044)
% 0.21/0.45  ipcrm: permission denied for id (802455614)
% 0.21/0.45  ipcrm: permission denied for id (799244351)
% 0.21/0.45  ipcrm: permission denied for id (802488384)
% 0.21/0.45  ipcrm: permission denied for id (799309889)
% 0.21/0.45  ipcrm: permission denied for id (799342658)
% 0.21/0.46  ipcrm: permission denied for id (799375427)
% 0.21/0.46  ipcrm: permission denied for id (799408196)
% 0.21/0.46  ipcrm: permission denied for id (802521157)
% 0.21/0.46  ipcrm: permission denied for id (802553926)
% 0.21/0.46  ipcrm: permission denied for id (802586695)
% 0.21/0.47  ipcrm: permission denied for id (799670348)
% 0.21/0.47  ipcrm: permission denied for id (799703117)
% 0.21/0.47  ipcrm: permission denied for id (799768655)
% 0.21/0.47  ipcrm: permission denied for id (799801424)
% 0.21/0.47  ipcrm: permission denied for id (799834193)
% 0.21/0.48  ipcrm: permission denied for id (799998038)
% 0.21/0.48  ipcrm: permission denied for id (800063576)
% 0.21/0.48  ipcrm: permission denied for id (802947161)
% 0.21/0.49  ipcrm: permission denied for id (802979930)
% 0.21/0.49  ipcrm: permission denied for id (803012699)
% 0.21/0.49  ipcrm: permission denied for id (800227421)
% 0.21/0.49  ipcrm: permission denied for id (800260190)
% 0.21/0.49  ipcrm: permission denied for id (800292959)
% 0.21/0.49  ipcrm: permission denied for id (803143776)
% 0.21/0.49  ipcrm: permission denied for id (800358497)
% 0.21/0.50  ipcrm: permission denied for id (803176547)
% 0.21/0.50  ipcrm: permission denied for id (800456804)
% 0.21/0.50  ipcrm: permission denied for id (803209317)
% 0.21/0.50  ipcrm: permission denied for id (800555111)
% 0.21/0.51  ipcrm: permission denied for id (800620649)
% 0.21/0.51  ipcrm: permission denied for id (803340395)
% 0.21/0.51  ipcrm: permission denied for id (803373164)
% 0.21/0.51  ipcrm: permission denied for id (800751725)
% 0.21/0.51  ipcrm: permission denied for id (800784494)
% 0.21/0.51  ipcrm: permission denied for id (800850032)
% 0.21/0.52  ipcrm: permission denied for id (800882801)
% 0.21/0.52  ipcrm: permission denied for id (800915570)
% 0.21/0.52  ipcrm: permission denied for id (803438707)
% 0.21/0.52  ipcrm: permission denied for id (801046645)
% 0.21/0.52  ipcrm: permission denied for id (801079414)
% 0.21/0.52  ipcrm: permission denied for id (801144952)
% 0.21/0.53  ipcrm: permission denied for id (803602555)
% 0.21/0.53  ipcrm: permission denied for id (803635324)
% 0.21/0.53  ipcrm: permission denied for id (801308797)
% 0.21/0.53  ipcrm: permission denied for id (801374335)
% 0.80/0.63  % (29607)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.80/0.64  % (29604)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.80/0.64  % (29619)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.80/0.64  % (29614)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.80/0.64  % (29619)Refutation found. Thanks to Tanya!
% 0.80/0.64  % SZS status Theorem for theBenchmark
% 0.80/0.64  % SZS output start Proof for theBenchmark
% 0.80/0.64  fof(f87,plain,(
% 0.80/0.64    $false),
% 0.80/0.64    inference(avatar_sat_refutation,[],[f43,f53,f58,f64,f69,f86])).
% 0.80/0.64  fof(f86,plain,(
% 0.80/0.64    ~spl0_3 | ~spl0_4 | ~spl0_5 | ~spl0_6),
% 0.80/0.64    inference(avatar_contradiction_clause,[],[f85])).
% 0.80/0.64  fof(f85,plain,(
% 0.80/0.64    $false | (~spl0_3 | ~spl0_4 | ~spl0_5 | ~spl0_6)),
% 0.80/0.64    inference(global_subsumption,[],[f18,f84])).
% 0.80/0.64  fof(f84,plain,(
% 0.80/0.64    k1_xboole_0 = k3_relat_1(k1_xboole_0) | (~spl0_3 | ~spl0_4 | ~spl0_5 | ~spl0_6)),
% 0.80/0.64    inference(forward_demodulation,[],[f83,f23])).
% 0.80/0.64  fof(f23,plain,(
% 0.80/0.64    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.80/0.64    inference(cnf_transformation,[],[f9])).
% 0.80/0.64  fof(f9,axiom,(
% 0.80/0.64    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.80/0.64  fof(f83,plain,(
% 0.80/0.64    k3_relat_1(k1_xboole_0) = k3_tarski(k1_zfmisc_1(k1_xboole_0)) | (~spl0_3 | ~spl0_4 | ~spl0_5 | ~spl0_6)),
% 0.80/0.64    inference(forward_demodulation,[],[f82,f68])).
% 0.80/0.64  fof(f68,plain,(
% 0.80/0.64    k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl0_6),
% 0.80/0.64    inference(avatar_component_clause,[],[f66])).
% 0.80/0.64  fof(f66,plain,(
% 0.80/0.64    spl0_6 <=> k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.80/0.64    introduced(avatar_definition,[new_symbols(naming,[spl0_6])])).
% 0.80/0.64  fof(f82,plain,(
% 0.80/0.64    k3_relat_1(k1_xboole_0) = k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (~spl0_3 | ~spl0_4 | ~spl0_5)),
% 0.80/0.64    inference(forward_demodulation,[],[f81,f52])).
% 0.80/0.64  fof(f52,plain,(
% 0.80/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl0_3),
% 0.80/0.64    inference(avatar_component_clause,[],[f50])).
% 0.80/0.64  fof(f50,plain,(
% 0.80/0.64    spl0_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.80/0.64    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).
% 0.80/0.64  fof(f81,plain,(
% 0.80/0.64    k3_relat_1(k1_xboole_0) = k3_tarski(k4_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl0_4 | ~spl0_5)),
% 0.80/0.64    inference(forward_demodulation,[],[f72,f57])).
% 0.80/0.64  fof(f57,plain,(
% 0.80/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl0_4),
% 0.80/0.64    inference(avatar_component_clause,[],[f55])).
% 0.80/0.64  fof(f55,plain,(
% 0.80/0.64    spl0_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.80/0.64    introduced(avatar_definition,[new_symbols(naming,[spl0_4])])).
% 0.80/0.64  fof(f72,plain,(
% 0.80/0.64    k3_relat_1(k1_xboole_0) = k3_tarski(k4_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))) | ~spl0_5),
% 0.80/0.64    inference(resolution,[],[f38,f63])).
% 0.80/0.64  fof(f63,plain,(
% 0.80/0.64    v1_relat_1(k1_xboole_0) | ~spl0_5),
% 0.80/0.64    inference(avatar_component_clause,[],[f61])).
% 0.80/0.64  fof(f61,plain,(
% 0.80/0.64    spl0_5 <=> v1_relat_1(k1_xboole_0)),
% 0.80/0.64    introduced(avatar_definition,[new_symbols(naming,[spl0_5])])).
% 0.80/0.64  fof(f38,plain,(
% 0.80/0.64    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k4_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.80/0.64    inference(definition_unfolding,[],[f26,f36])).
% 0.80/0.64  fof(f36,plain,(
% 0.80/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.80/0.64    inference(definition_unfolding,[],[f27,f34])).
% 0.80/0.64  fof(f34,plain,(
% 0.80/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.80/0.64    inference(definition_unfolding,[],[f28,f33])).
% 0.80/0.64  fof(f33,plain,(
% 0.80/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.80/0.64    inference(definition_unfolding,[],[f29,f32])).
% 0.80/0.64  fof(f32,plain,(
% 0.80/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.80/0.64    inference(definition_unfolding,[],[f30,f31])).
% 0.80/0.64  fof(f31,plain,(
% 0.80/0.64    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.80/0.64    inference(cnf_transformation,[],[f6])).
% 0.80/0.64  fof(f6,axiom,(
% 0.80/0.64    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.80/0.64  fof(f30,plain,(
% 0.80/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.80/0.64    inference(cnf_transformation,[],[f5])).
% 0.80/0.64  fof(f5,axiom,(
% 0.80/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.80/0.64  fof(f29,plain,(
% 0.80/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.80/0.64    inference(cnf_transformation,[],[f4])).
% 0.80/0.64  fof(f4,axiom,(
% 0.80/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.80/0.64  fof(f28,plain,(
% 0.80/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.80/0.64    inference(cnf_transformation,[],[f3])).
% 0.80/0.64  fof(f3,axiom,(
% 0.80/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.80/0.64  fof(f27,plain,(
% 0.80/0.64    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.80/0.64    inference(cnf_transformation,[],[f7])).
% 0.80/0.64  fof(f7,axiom,(
% 0.80/0.64    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.80/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.80/0.64  fof(f26,plain,(
% 0.80/0.64    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.80/0.64    inference(cnf_transformation,[],[f17])).
% 0.80/0.65  fof(f17,plain,(
% 0.80/0.65    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.80/0.65    inference(ennf_transformation,[],[f11])).
% 0.80/0.65  fof(f11,axiom,(
% 0.80/0.65    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.80/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.80/0.65  fof(f18,plain,(
% 0.80/0.65    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.80/0.65    inference(cnf_transformation,[],[f15])).
% 0.80/0.65  fof(f15,plain,(
% 0.80/0.65    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.80/0.65    inference(flattening,[],[f14])).
% 0.80/0.65  fof(f14,negated_conjecture,(
% 0.80/0.65    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.80/0.65    inference(negated_conjecture,[],[f13])).
% 0.80/0.65  fof(f13,conjecture,(
% 0.80/0.65    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.80/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.80/0.65  fof(f69,plain,(
% 0.80/0.65    spl0_6),
% 0.80/0.65    inference(avatar_split_clause,[],[f37,f66])).
% 0.80/0.65  fof(f37,plain,(
% 0.80/0.65    k1_zfmisc_1(k1_xboole_0) = k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.80/0.65    inference(definition_unfolding,[],[f20,f35])).
% 0.80/0.65  fof(f35,plain,(
% 0.80/0.65    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.80/0.65    inference(definition_unfolding,[],[f24,f34])).
% 0.80/0.65  fof(f24,plain,(
% 0.80/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.80/0.65    inference(cnf_transformation,[],[f2])).
% 0.80/0.65  fof(f2,axiom,(
% 0.80/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.80/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.80/0.65  fof(f20,plain,(
% 0.80/0.65    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.80/0.65    inference(cnf_transformation,[],[f8])).
% 0.80/0.65  fof(f8,axiom,(
% 0.80/0.65    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.80/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.80/0.65  fof(f64,plain,(
% 0.80/0.65    spl0_5 | ~spl0_1),
% 0.80/0.65    inference(avatar_split_clause,[],[f59,f40,f61])).
% 0.80/0.65  fof(f40,plain,(
% 0.80/0.65    spl0_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.80/0.65    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).
% 0.80/0.65  fof(f59,plain,(
% 0.80/0.65    v1_relat_1(k1_xboole_0) | ~spl0_1),
% 0.80/0.65    inference(unit_resulting_resolution,[],[f42,f25])).
% 0.80/0.65  fof(f25,plain,(
% 0.80/0.65    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.80/0.65    inference(cnf_transformation,[],[f16])).
% 0.80/0.65  fof(f16,plain,(
% 0.80/0.65    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.80/0.65    inference(ennf_transformation,[],[f10])).
% 0.80/0.65  fof(f10,axiom,(
% 0.80/0.65    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.80/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.80/0.65  fof(f42,plain,(
% 0.80/0.65    v1_xboole_0(k1_xboole_0) | ~spl0_1),
% 0.80/0.65    inference(avatar_component_clause,[],[f40])).
% 0.80/0.65  fof(f58,plain,(
% 0.80/0.65    spl0_4),
% 0.80/0.65    inference(avatar_split_clause,[],[f22,f55])).
% 0.80/0.65  fof(f22,plain,(
% 0.80/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.80/0.65    inference(cnf_transformation,[],[f12])).
% 0.80/0.65  fof(f12,axiom,(
% 0.80/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.80/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.80/0.65  fof(f53,plain,(
% 0.80/0.65    spl0_3),
% 0.80/0.65    inference(avatar_split_clause,[],[f21,f50])).
% 0.80/0.65  fof(f21,plain,(
% 0.80/0.65    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.80/0.65    inference(cnf_transformation,[],[f12])).
% 0.80/0.65  fof(f43,plain,(
% 0.80/0.65    spl0_1),
% 0.80/0.65    inference(avatar_split_clause,[],[f19,f40])).
% 0.80/0.65  fof(f19,plain,(
% 0.80/0.65    v1_xboole_0(k1_xboole_0)),
% 0.80/0.65    inference(cnf_transformation,[],[f1])).
% 0.80/0.65  fof(f1,axiom,(
% 0.80/0.65    v1_xboole_0(k1_xboole_0)),
% 0.80/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.80/0.65  % SZS output end Proof for theBenchmark
% 0.80/0.65  % (29619)------------------------------
% 0.80/0.65  % (29619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.80/0.65  % (29619)Termination reason: Refutation
% 0.80/0.65  
% 0.80/0.65  % (29619)Memory used [KB]: 10618
% 0.80/0.65  % (29619)Time elapsed: 0.061 s
% 0.80/0.65  % (29619)------------------------------
% 0.80/0.65  % (29619)------------------------------
% 0.80/0.65  % (29373)Success in time 0.284 s
%------------------------------------------------------------------------------
