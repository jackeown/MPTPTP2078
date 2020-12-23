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
% DateTime   : Thu Dec  3 12:41:08 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 144 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  172 ( 320 expanded)
%              Number of equality atoms :   49 ( 101 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f51,f162,f170,f183,f251,f354])).

fof(f354,plain,
    ( ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f314,f264])).

fof(f264,plain,
    ( ! [X0] : sK0 = X0
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(resolution,[],[f219,f189])).

fof(f189,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k1_xboole_0,k1_tarski(X3))
        | sK0 = X3 )
    | ~ spl2_6 ),
    inference(superposition,[],[f33,f180])).

fof(f180,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl2_6
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f219,plain,
    ( ! [X8] : r1_tarski(k1_xboole_0,X8)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl2_8
  <=> ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f314,plain,
    ( k1_xboole_0 != sK0
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f53,f264])).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_tarski(X0,X1) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f251,plain,
    ( spl2_8
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f245,f178,f218])).

fof(f245,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f242,f180])).

fof(f242,plain,
    ( ! [X0] : r1_tarski(k1_tarski(sK0),X0)
    | ~ spl2_6 ),
    inference(resolution,[],[f234,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_tarski(X0))
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(superposition,[],[f73,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f36,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f234,plain,
    ( ! [X0] : ~ r2_hidden(sK0,X0)
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f233,f191])).

fof(f191,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK0,X5)
        | r1_tarski(k1_xboole_0,X5) )
    | ~ spl2_6 ),
    inference(superposition,[],[f60,f180])).

fof(f60,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_tarski(X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(superposition,[],[f40,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f233,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f230])).

fof(f230,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r2_hidden(sK0,X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl2_6 ),
    inference(superposition,[],[f186,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f121,f39])).

fof(f39,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1)
      | r2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ) ),
    inference(resolution,[],[f77,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f36,f35])).

fof(f186,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)
        | ~ r2_hidden(sK0,X0) )
    | ~ spl2_6 ),
    inference(superposition,[],[f29,f180])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f183,plain,
    ( spl2_6
    | ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f182,f47,f43,f178])).

fof(f43,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f182,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f173,f49])).

fof(f49,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f173,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f30,f44])).

fof(f44,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f170,plain,
    ( ~ spl2_2
    | spl2_5 ),
    inference(avatar_split_clause,[],[f165,f159,f47])).

fof(f159,plain,
    ( spl2_5
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f165,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_5 ),
    inference(resolution,[],[f161,f60])).

fof(f161,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f162,plain,
    ( ~ spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f153,f43,f159])).

fof(f153,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f150])).

fof(f150,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_1 ),
    inference(superposition,[],[f45,f123])).

fof(f45,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f51,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f27,f47,f43])).

fof(f27,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f50,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f28,f47,f43])).

fof(f28,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (733872128)
% 0.13/0.36  ipcrm: permission denied for id (733904898)
% 0.13/0.36  ipcrm: permission denied for id (733937668)
% 0.20/0.37  ipcrm: permission denied for id (734101512)
% 0.20/0.37  ipcrm: permission denied for id (737378313)
% 0.20/0.37  ipcrm: permission denied for id (737411082)
% 0.20/0.37  ipcrm: permission denied for id (734199819)
% 0.20/0.37  ipcrm: permission denied for id (737443852)
% 0.20/0.37  ipcrm: permission denied for id (737476621)
% 0.20/0.38  ipcrm: permission denied for id (734363663)
% 0.20/0.38  ipcrm: permission denied for id (737542160)
% 0.20/0.38  ipcrm: permission denied for id (734429201)
% 0.20/0.38  ipcrm: permission denied for id (734461970)
% 0.20/0.38  ipcrm: permission denied for id (734494739)
% 0.20/0.38  ipcrm: permission denied for id (734560277)
% 0.20/0.39  ipcrm: permission denied for id (734593047)
% 0.20/0.39  ipcrm: permission denied for id (734625816)
% 0.20/0.39  ipcrm: permission denied for id (737673242)
% 0.20/0.39  ipcrm: permission denied for id (737706011)
% 0.20/0.39  ipcrm: permission denied for id (734691356)
% 0.20/0.39  ipcrm: permission denied for id (737738781)
% 0.20/0.39  ipcrm: permission denied for id (737771550)
% 0.20/0.40  ipcrm: permission denied for id (737869857)
% 0.20/0.40  ipcrm: permission denied for id (737902626)
% 0.20/0.40  ipcrm: permission denied for id (734855205)
% 0.20/0.40  ipcrm: permission denied for id (738033703)
% 0.20/0.41  ipcrm: permission denied for id (734920744)
% 0.20/0.41  ipcrm: permission denied for id (738066473)
% 0.20/0.41  ipcrm: permission denied for id (734986282)
% 0.20/0.41  ipcrm: permission denied for id (738132012)
% 0.20/0.41  ipcrm: permission denied for id (735051821)
% 0.20/0.41  ipcrm: permission denied for id (735084590)
% 0.20/0.41  ipcrm: permission denied for id (735117359)
% 0.20/0.42  ipcrm: permission denied for id (738164784)
% 0.20/0.42  ipcrm: permission denied for id (735182898)
% 0.20/0.42  ipcrm: permission denied for id (738230323)
% 0.20/0.42  ipcrm: permission denied for id (735248436)
% 0.20/0.42  ipcrm: permission denied for id (735313974)
% 0.20/0.42  ipcrm: permission denied for id (738295863)
% 0.20/0.43  ipcrm: permission denied for id (735445050)
% 0.20/0.43  ipcrm: permission denied for id (735510588)
% 0.20/0.43  ipcrm: permission denied for id (738426941)
% 0.20/0.43  ipcrm: permission denied for id (735543358)
% 0.20/0.43  ipcrm: permission denied for id (735608896)
% 0.20/0.44  ipcrm: permission denied for id (738492481)
% 0.20/0.44  ipcrm: permission denied for id (738525250)
% 0.20/0.44  ipcrm: permission denied for id (735739973)
% 0.20/0.44  ipcrm: permission denied for id (735772742)
% 0.20/0.44  ipcrm: permission denied for id (735805511)
% 0.20/0.44  ipcrm: permission denied for id (735871049)
% 0.20/0.45  ipcrm: permission denied for id (735936587)
% 0.20/0.45  ipcrm: permission denied for id (735969356)
% 0.20/0.45  ipcrm: permission denied for id (736002125)
% 0.20/0.45  ipcrm: permission denied for id (736034894)
% 0.20/0.45  ipcrm: permission denied for id (738721871)
% 0.20/0.45  ipcrm: permission denied for id (736067664)
% 0.20/0.45  ipcrm: permission denied for id (736133201)
% 0.20/0.46  ipcrm: permission denied for id (736165970)
% 0.20/0.46  ipcrm: permission denied for id (738754643)
% 0.20/0.46  ipcrm: permission denied for id (738787412)
% 0.20/0.46  ipcrm: permission denied for id (736231509)
% 0.20/0.46  ipcrm: permission denied for id (736264278)
% 0.20/0.46  ipcrm: permission denied for id (738820183)
% 0.20/0.46  ipcrm: permission denied for id (736362584)
% 0.20/0.47  ipcrm: permission denied for id (736460891)
% 0.20/0.47  ipcrm: permission denied for id (736493660)
% 0.20/0.47  ipcrm: permission denied for id (738918493)
% 0.20/0.47  ipcrm: permission denied for id (736526430)
% 0.20/0.47  ipcrm: permission denied for id (738951263)
% 0.20/0.47  ipcrm: permission denied for id (738984032)
% 0.20/0.47  ipcrm: permission denied for id (739082339)
% 0.20/0.48  ipcrm: permission denied for id (739115108)
% 0.20/0.48  ipcrm: permission denied for id (739180646)
% 0.20/0.48  ipcrm: permission denied for id (736723049)
% 0.20/0.49  ipcrm: permission denied for id (736821357)
% 0.20/0.49  ipcrm: permission denied for id (736854126)
% 0.20/0.49  ipcrm: permission denied for id (739377263)
% 0.20/0.49  ipcrm: permission denied for id (736919664)
% 0.20/0.49  ipcrm: permission denied for id (736952433)
% 0.20/0.49  ipcrm: permission denied for id (739410034)
% 0.20/0.49  ipcrm: permission denied for id (736985204)
% 0.20/0.50  ipcrm: permission denied for id (739475573)
% 0.20/0.50  ipcrm: permission denied for id (737017974)
% 0.68/0.64  % (3738)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.68/0.65  % (3748)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.23/0.65  % (3756)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.23/0.66  % (3759)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.23/0.66  % (3759)Refutation not found, incomplete strategy% (3759)------------------------------
% 1.23/0.66  % (3759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.66  % (3759)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.66  
% 1.23/0.66  % (3759)Memory used [KB]: 10618
% 1.23/0.66  % (3759)Time elapsed: 0.108 s
% 1.23/0.66  % (3759)------------------------------
% 1.23/0.66  % (3759)------------------------------
% 1.23/0.66  % (3736)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.66  % (3736)Refutation not found, incomplete strategy% (3736)------------------------------
% 1.23/0.66  % (3736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.66  % (3736)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.66  
% 1.23/0.66  % (3736)Memory used [KB]: 1663
% 1.23/0.66  % (3736)Time elapsed: 0.107 s
% 1.23/0.66  % (3736)------------------------------
% 1.23/0.66  % (3736)------------------------------
% 1.23/0.67  % (3737)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.35/0.67  % (3756)Refutation found. Thanks to Tanya!
% 1.35/0.67  % SZS status Theorem for theBenchmark
% 1.35/0.67  % SZS output start Proof for theBenchmark
% 1.35/0.67  fof(f355,plain,(
% 1.35/0.67    $false),
% 1.35/0.67    inference(avatar_sat_refutation,[],[f50,f51,f162,f170,f183,f251,f354])).
% 1.35/0.67  fof(f354,plain,(
% 1.35/0.67    ~spl2_6 | ~spl2_8),
% 1.35/0.67    inference(avatar_contradiction_clause,[],[f353])).
% 1.35/0.67  fof(f353,plain,(
% 1.35/0.67    $false | (~spl2_6 | ~spl2_8)),
% 1.35/0.67    inference(subsumption_resolution,[],[f314,f264])).
% 1.35/0.67  fof(f264,plain,(
% 1.35/0.67    ( ! [X0] : (sK0 = X0) ) | (~spl2_6 | ~spl2_8)),
% 1.35/0.67    inference(resolution,[],[f219,f189])).
% 1.35/0.67  fof(f189,plain,(
% 1.35/0.67    ( ! [X3] : (~r1_tarski(k1_xboole_0,k1_tarski(X3)) | sK0 = X3) ) | ~spl2_6),
% 1.35/0.67    inference(superposition,[],[f33,f180])).
% 1.35/0.67  fof(f180,plain,(
% 1.35/0.67    k1_xboole_0 = k1_tarski(sK0) | ~spl2_6),
% 1.35/0.67    inference(avatar_component_clause,[],[f178])).
% 1.35/0.67  fof(f178,plain,(
% 1.35/0.67    spl2_6 <=> k1_xboole_0 = k1_tarski(sK0)),
% 1.35/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.35/0.67  fof(f33,plain,(
% 1.35/0.67    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.35/0.67    inference(cnf_transformation,[],[f20])).
% 1.35/0.67  fof(f20,plain,(
% 1.35/0.67    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.35/0.67    inference(ennf_transformation,[],[f12])).
% 1.35/0.67  fof(f12,axiom,(
% 1.35/0.67    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.35/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.35/0.67  fof(f219,plain,(
% 1.35/0.67    ( ! [X8] : (r1_tarski(k1_xboole_0,X8)) ) | ~spl2_8),
% 1.35/0.67    inference(avatar_component_clause,[],[f218])).
% 1.35/0.67  fof(f218,plain,(
% 1.35/0.67    spl2_8 <=> ! [X8] : r1_tarski(k1_xboole_0,X8)),
% 1.35/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.35/0.67  fof(f314,plain,(
% 1.35/0.67    k1_xboole_0 != sK0 | (~spl2_6 | ~spl2_8)),
% 1.35/0.67    inference(superposition,[],[f53,f264])).
% 1.35/0.67  fof(f53,plain,(
% 1.35/0.67    ( ! [X0,X1] : (k1_xboole_0 != k2_tarski(X0,X1)) )),
% 1.35/0.67    inference(superposition,[],[f38,f35])).
% 1.35/0.67  fof(f35,plain,(
% 1.35/0.67    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.67    inference(cnf_transformation,[],[f4])).
% 1.35/0.67  fof(f4,axiom,(
% 1.35/0.67    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.35/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.35/0.67  fof(f38,plain,(
% 1.35/0.67    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.35/0.67    inference(cnf_transformation,[],[f10])).
% 1.35/0.67  fof(f10,axiom,(
% 1.35/0.67    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.35/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.35/0.67  fof(f251,plain,(
% 1.35/0.67    spl2_8 | ~spl2_6),
% 1.35/0.67    inference(avatar_split_clause,[],[f245,f178,f218])).
% 1.35/0.67  fof(f245,plain,(
% 1.35/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_6),
% 1.35/0.67    inference(forward_demodulation,[],[f242,f180])).
% 1.35/0.67  fof(f242,plain,(
% 1.35/0.67    ( ! [X0] : (r1_tarski(k1_tarski(sK0),X0)) ) | ~spl2_6),
% 1.35/0.67    inference(resolution,[],[f234,f82])).
% 1.35/0.67  fof(f82,plain,(
% 1.35/0.67    ( ! [X0,X1] : (r2_hidden(X0,k1_tarski(X0)) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.35/0.67    inference(superposition,[],[f73,f30])).
% 1.35/0.67  fof(f30,plain,(
% 1.35/0.67    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.35/0.67    inference(cnf_transformation,[],[f26])).
% 1.35/0.67  fof(f26,plain,(
% 1.35/0.67    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.35/0.67    inference(nnf_transformation,[],[f11])).
% 1.35/0.67  fof(f11,axiom,(
% 1.35/0.67    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.35/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.35/0.67  fof(f73,plain,(
% 1.35/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 1.35/0.67    inference(resolution,[],[f36,f40])).
% 1.35/0.67  fof(f40,plain,(
% 1.35/0.67    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.35/0.67    inference(cnf_transformation,[],[f7])).
% 1.35/0.67  fof(f7,axiom,(
% 1.35/0.67    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.35/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.35/0.67  fof(f36,plain,(
% 1.35/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.35/0.67    inference(cnf_transformation,[],[f21])).
% 1.35/0.67  fof(f21,plain,(
% 1.35/0.67    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.35/0.67    inference(ennf_transformation,[],[f5])).
% 1.35/0.67  fof(f5,axiom,(
% 1.35/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.35/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.35/0.67  fof(f234,plain,(
% 1.35/0.67    ( ! [X0] : (~r2_hidden(sK0,X0)) ) | ~spl2_6),
% 1.35/0.67    inference(subsumption_resolution,[],[f233,f191])).
% 1.35/0.67  fof(f191,plain,(
% 1.35/0.67    ( ! [X5] : (~r2_hidden(sK0,X5) | r1_tarski(k1_xboole_0,X5)) ) | ~spl2_6),
% 1.35/0.67    inference(superposition,[],[f60,f180])).
% 1.35/0.67  fof(f60,plain,(
% 1.35/0.67    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),X2) | ~r2_hidden(X1,X2)) )),
% 1.35/0.67    inference(superposition,[],[f40,f31])).
% 1.35/0.67  fof(f31,plain,(
% 1.35/0.67    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 1.35/0.67    inference(cnf_transformation,[],[f17])).
% 1.35/0.67  fof(f17,plain,(
% 1.35/0.67    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.35/0.67    inference(ennf_transformation,[],[f9])).
% 1.35/0.67  fof(f9,axiom,(
% 1.35/0.67    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.35/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.35/0.67  fof(f233,plain,(
% 1.35/0.67    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_tarski(k1_xboole_0,X0)) ) | ~spl2_6),
% 1.35/0.67    inference(trivial_inequality_removal,[],[f230])).
% 1.35/0.67  fof(f230,plain,(
% 1.35/0.67    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,X0) | ~r1_tarski(k1_xboole_0,X0)) ) | ~spl2_6),
% 1.35/0.67    inference(superposition,[],[f186,f123])).
% 1.35/0.67  fof(f123,plain,(
% 1.35/0.67    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.35/0.67    inference(subsumption_resolution,[],[f121,f39])).
% 1.35/0.67  fof(f39,plain,(
% 1.35/0.67    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0)) )),
% 1.35/0.67    inference(cnf_transformation,[],[f6])).
% 1.35/0.67  fof(f6,axiom,(
% 1.35/0.67    ! [X0] : ~r2_xboole_0(X0,k1_xboole_0)),
% 1.35/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).
% 1.35/0.67  fof(f121,plain,(
% 1.35/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1) | r2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 1.35/0.67    inference(resolution,[],[f77,f32])).
% 1.35/0.67  fof(f32,plain,(
% 1.35/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.35/0.67    inference(cnf_transformation,[],[f19])).
% 1.35/0.67  fof(f19,plain,(
% 1.35/0.67    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.35/0.67    inference(flattening,[],[f18])).
% 1.35/0.67  fof(f18,plain,(
% 1.35/0.67    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 1.35/0.67    inference(ennf_transformation,[],[f15])).
% 1.35/0.67  fof(f15,plain,(
% 1.35/0.67    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 1.35/0.67    inference(unused_predicate_definition_removal,[],[f2])).
% 1.35/0.67  fof(f2,axiom,(
% 1.35/0.67    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.35/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.35/0.67  fof(f77,plain,(
% 1.35/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0) | ~r1_tarski(X1,X0)) )),
% 1.35/0.67    inference(superposition,[],[f36,f35])).
% 1.35/0.67  fof(f186,plain,(
% 1.35/0.67    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) | ~r2_hidden(sK0,X0)) ) | ~spl2_6),
% 1.35/0.67    inference(superposition,[],[f29,f180])).
% 1.35/0.67  fof(f29,plain,(
% 1.35/0.67    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.35/0.67    inference(cnf_transformation,[],[f26])).
% 1.35/0.67  fof(f183,plain,(
% 1.35/0.67    spl2_6 | ~spl2_1 | spl2_2),
% 1.35/0.67    inference(avatar_split_clause,[],[f182,f47,f43,f178])).
% 1.35/0.67  fof(f43,plain,(
% 1.35/0.67    spl2_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.35/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.35/0.67  fof(f47,plain,(
% 1.35/0.67    spl2_2 <=> r2_hidden(sK0,sK1)),
% 1.35/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.35/0.67  fof(f182,plain,(
% 1.35/0.67    k1_xboole_0 = k1_tarski(sK0) | (~spl2_1 | spl2_2)),
% 1.35/0.67    inference(subsumption_resolution,[],[f173,f49])).
% 1.35/0.67  fof(f49,plain,(
% 1.35/0.67    ~r2_hidden(sK0,sK1) | spl2_2),
% 1.35/0.67    inference(avatar_component_clause,[],[f47])).
% 1.35/0.67  fof(f173,plain,(
% 1.35/0.67    k1_xboole_0 = k1_tarski(sK0) | r2_hidden(sK0,sK1) | ~spl2_1),
% 1.35/0.67    inference(superposition,[],[f30,f44])).
% 1.35/0.67  fof(f44,plain,(
% 1.35/0.67    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl2_1),
% 1.35/0.67    inference(avatar_component_clause,[],[f43])).
% 1.35/0.67  fof(f170,plain,(
% 1.35/0.67    ~spl2_2 | spl2_5),
% 1.35/0.67    inference(avatar_split_clause,[],[f165,f159,f47])).
% 1.35/0.67  fof(f159,plain,(
% 1.35/0.67    spl2_5 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 1.35/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.35/0.67  fof(f165,plain,(
% 1.35/0.67    ~r2_hidden(sK0,sK1) | spl2_5),
% 1.35/0.67    inference(resolution,[],[f161,f60])).
% 1.35/0.67  fof(f161,plain,(
% 1.35/0.67    ~r1_tarski(k1_tarski(sK0),sK1) | spl2_5),
% 1.35/0.67    inference(avatar_component_clause,[],[f159])).
% 1.35/0.67  fof(f162,plain,(
% 1.35/0.67    ~spl2_5 | spl2_1),
% 1.35/0.67    inference(avatar_split_clause,[],[f153,f43,f159])).
% 1.35/0.67  fof(f153,plain,(
% 1.35/0.67    ~r1_tarski(k1_tarski(sK0),sK1) | spl2_1),
% 1.35/0.67    inference(trivial_inequality_removal,[],[f150])).
% 1.35/0.67  fof(f150,plain,(
% 1.35/0.67    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_tarski(sK0),sK1) | spl2_1),
% 1.35/0.67    inference(superposition,[],[f45,f123])).
% 1.35/0.67  fof(f45,plain,(
% 1.35/0.67    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl2_1),
% 1.35/0.67    inference(avatar_component_clause,[],[f43])).
% 1.35/0.67  fof(f51,plain,(
% 1.35/0.67    spl2_1 | spl2_2),
% 1.35/0.67    inference(avatar_split_clause,[],[f27,f47,f43])).
% 1.35/0.67  fof(f27,plain,(
% 1.35/0.67    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.35/0.67    inference(cnf_transformation,[],[f25])).
% 1.35/0.67  fof(f25,plain,(
% 1.35/0.67    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.35/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 1.35/0.67  fof(f24,plain,(
% 1.35/0.67    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.35/0.67    introduced(choice_axiom,[])).
% 1.35/0.67  fof(f23,plain,(
% 1.35/0.67    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.35/0.67    inference(nnf_transformation,[],[f16])).
% 1.35/0.67  fof(f16,plain,(
% 1.35/0.67    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 1.35/0.67    inference(ennf_transformation,[],[f14])).
% 1.35/0.67  fof(f14,negated_conjecture,(
% 1.35/0.67    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.35/0.67    inference(negated_conjecture,[],[f13])).
% 1.35/0.67  fof(f13,conjecture,(
% 1.35/0.67    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.35/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 1.35/0.67  fof(f50,plain,(
% 1.35/0.67    ~spl2_1 | ~spl2_2),
% 1.35/0.67    inference(avatar_split_clause,[],[f28,f47,f43])).
% 1.35/0.67  fof(f28,plain,(
% 1.35/0.67    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.35/0.67    inference(cnf_transformation,[],[f25])).
% 1.35/0.67  % SZS output end Proof for theBenchmark
% 1.35/0.67  % (3756)------------------------------
% 1.35/0.67  % (3756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.67  % (3756)Termination reason: Refutation
% 1.35/0.67  
% 1.35/0.67  % (3756)Memory used [KB]: 6396
% 1.35/0.67  % (3756)Time elapsed: 0.117 s
% 1.35/0.67  % (3756)------------------------------
% 1.35/0.67  % (3756)------------------------------
% 1.35/0.68  % (3546)Success in time 0.321 s
%------------------------------------------------------------------------------
