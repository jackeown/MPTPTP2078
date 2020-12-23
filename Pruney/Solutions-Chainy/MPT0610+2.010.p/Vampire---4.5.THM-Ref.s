%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 118 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :    8
%              Number of atoms          :  168 ( 320 expanded)
%              Number of equality atoms :   40 (  58 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f76,f83,f97,f243,f283])).

fof(f283,plain,
    ( spl2_7
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f281,f204,f80])).

fof(f80,plain,
    ( spl2_7
  <=> k1_xboole_0 = k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f204,plain,
    ( spl2_22
  <=> k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f281,plain,
    ( k1_xboole_0 = k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ spl2_22 ),
    inference(superposition,[],[f25,f206])).

fof(f206,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))),k1_xboole_0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f243,plain,
    ( spl2_22
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f242,f93,f55,f50,f204])).

fof(f50,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f55,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f93,plain,
    ( spl2_9
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f242,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))),k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f210,f95])).

fof(f95,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f210,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))),k1_setfam_1(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1))))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f57,f52,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_setfam_1(k2_tarski(X1,X0))),k1_setfam_1(k2_tarski(k1_relat_1(X1),k1_relat_1(X0)))) ) ),
    inference(resolution,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k1_relat_1(X0),k1_relat_1(X1))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f28,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f52,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f57,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f97,plain,
    ( spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f91,f45,f93])).

fof(f45,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f91,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1)))
    | ~ spl2_2 ),
    inference(resolution,[],[f38,f47])).

fof(f47,plain,
    ( r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f83,plain,
    ( ~ spl2_7
    | ~ spl2_4
    | spl2_6 ),
    inference(avatar_split_clause,[],[f78,f73,f55,f80])).

fof(f73,plain,
    ( spl2_6
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f78,plain,
    ( k1_xboole_0 != k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ spl2_4
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f60,f75,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

% (7882)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f75,plain,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(sK0,sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f60,plain,
    ( ! [X0] : v1_relat_1(k1_setfam_1(k2_tarski(sK0,X0)))
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f76,plain,
    ( ~ spl2_6
    | spl2_1 ),
    inference(avatar_split_clause,[],[f71,f40,f73])).

fof(f40,plain,
    ( spl2_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f71,plain,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(sK0,sK1))
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f42,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f58,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

fof(f53,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f50])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f24,f40])).

fof(f24,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (7890)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.44  % (7886)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.44  % (7886)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f284,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f43,f48,f53,f58,f76,f83,f97,f243,f283])).
% 0.21/0.44  fof(f283,plain,(
% 0.21/0.44    spl2_7 | ~spl2_22),
% 0.21/0.44    inference(avatar_split_clause,[],[f281,f204,f80])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    spl2_7 <=> k1_xboole_0 = k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.44  fof(f204,plain,(
% 0.21/0.44    spl2_22 <=> k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))),k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.44  fof(f281,plain,(
% 0.21/0.44    k1_xboole_0 = k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))) | ~spl2_22),
% 0.21/0.44    inference(superposition,[],[f25,f206])).
% 0.21/0.44  fof(f206,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))),k1_xboole_0) | ~spl2_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f204])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.44  fof(f243,plain,(
% 0.21/0.44    spl2_22 | ~spl2_3 | ~spl2_4 | ~spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f242,f93,f55,f50,f204])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl2_4 <=> v1_relat_1(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    spl2_9 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f242,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))),k1_xboole_0) | (~spl2_3 | ~spl2_4 | ~spl2_9)),
% 0.21/0.44    inference(forward_demodulation,[],[f210,f95])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) | ~spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f93])).
% 0.21/0.44  fof(f210,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))),k1_setfam_1(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1)))) | (~spl2_3 | ~spl2_4)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f57,f52,f123])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_xboole_0 = k4_xboole_0(k1_relat_1(k1_setfam_1(k2_tarski(X1,X0))),k1_setfam_1(k2_tarski(k1_relat_1(X1),k1_relat_1(X0))))) )),
% 0.21/0.44    inference(resolution,[],[f35,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k1_relat_1(X0),k1_relat_1(X1)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f28,f29,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    v1_relat_1(sK1) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f50])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    v1_relat_1(sK0) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f55])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    spl2_9 | ~spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f91,f45,f93])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl2_2 <=> r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f91,plain,(
% 0.21/0.44    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) | ~spl2_2),
% 0.21/0.44    inference(resolution,[],[f38,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f31,f29])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ~spl2_7 | ~spl2_4 | spl2_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f78,f73,f55,f80])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    spl2_6 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    k1_xboole_0 != k1_relat_1(k1_setfam_1(k2_tarski(sK0,sK1))) | (~spl2_4 | spl2_6)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f60,f75,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  % (7882)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    k1_xboole_0 != k1_setfam_1(k2_tarski(sK0,sK1)) | spl2_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f73])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X0] : (v1_relat_1(k1_setfam_1(k2_tarski(sK0,X0)))) ) | ~spl2_4),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f57,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f30,f29])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ~spl2_6 | spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f71,f40,f73])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    spl2_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    k1_xboole_0 != k1_setfam_1(k2_tarski(sK0,sK1)) | spl2_1),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f42,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f32,f29])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,sK1) | spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f40])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f21,f55])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17,f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(flattening,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.45    inference(negated_conjecture,[],[f8])).
% 0.21/0.45  fof(f8,conjecture,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f50])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    spl2_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f45])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f40])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (7886)------------------------------
% 0.21/0.45  % (7886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (7886)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (7886)Memory used [KB]: 6396
% 0.21/0.45  % (7886)Time elapsed: 0.046 s
% 0.21/0.45  % (7886)------------------------------
% 0.21/0.45  % (7886)------------------------------
% 0.21/0.45  % (7879)Success in time 0.093 s
%------------------------------------------------------------------------------
