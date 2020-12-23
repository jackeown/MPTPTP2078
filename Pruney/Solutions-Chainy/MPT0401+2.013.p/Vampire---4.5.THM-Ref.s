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
% DateTime   : Thu Dec  3 12:46:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 132 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  127 ( 232 expanded)
%              Number of equality atoms :   21 (  64 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f103,f197,f215])).

fof(f215,plain,
    ( spl3_1
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f214,f142,f49])).

fof(f49,plain,
    ( spl3_1
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f142,plain,
    ( spl3_14
  <=> r1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f214,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f202,f45])).

fof(f45,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f202,plain,
    ( r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),sK0)
    | ~ spl3_14 ),
    inference(resolution,[],[f144,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_setfam_1(X1,k4_enumset1(X0,X0,X0,X0,X0,X0))
      | r1_tarski(k3_tarski(X1),X0) ) ),
    inference(superposition,[],[f32,f45])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f144,plain,
    ( r1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f197,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f194,f100,f59,f142])).

fof(f59,plain,
    ( spl3_3
  <=> r1_setfam_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( spl3_9
  <=> r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f194,plain,
    ( r1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f137,f102])).

fof(f102,plain,
    ( r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_setfam_1(X0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f76,f61])).

fof(f61,plain,
    ( r1_setfam_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f76,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_setfam_1(X1,X2)
      | r1_setfam_1(X3,X2)
      | ~ r1_tarski(X3,X1) ) ),
    inference(resolution,[],[f36,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r1_setfam_1(X1,X2)
      | r1_setfam_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X0,X2)
      | ~ r1_setfam_1(X1,X2)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X0,X2)
      | ~ r1_setfam_1(X1,X2)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
     => r1_setfam_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_setfam_1)).

fof(f103,plain,
    ( spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f98,f54,f100])).

fof(f54,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f98,plain,
    ( r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f56,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f56,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f62,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f44,f59])).

fof(f44,plain,(
    r1_setfam_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f24,f43])).

fof(f24,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK2,sK0)
    & r2_hidden(sK2,sK1)
    & r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK0)
          & r2_hidden(X2,sK1) )
      & r1_setfam_1(sK1,k1_tarski(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK0)
        & r2_hidden(X2,sK1) )
   => ( ~ r1_tarski(sK2,sK0)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:25:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (15133)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.45  % (15133)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f216,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f52,f57,f62,f103,f197,f215])).
% 0.22/0.45  fof(f215,plain,(
% 0.22/0.45    spl3_1 | ~spl3_14),
% 0.22/0.45    inference(avatar_split_clause,[],[f214,f142,f49])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    spl3_1 <=> r1_tarski(sK2,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f142,plain,(
% 0.22/0.45    spl3_14 <=> r1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.45  fof(f214,plain,(
% 0.22/0.45    r1_tarski(sK2,sK0) | ~spl3_14),
% 0.22/0.45    inference(forward_demodulation,[],[f202,f45])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.22/0.45    inference(definition_unfolding,[],[f28,f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f29,f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f30,f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f35,f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f37,f38])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.45    inference(rectify,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.45  fof(f202,plain,(
% 0.22/0.45    r1_tarski(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),sK0) | ~spl3_14),
% 0.22/0.45    inference(resolution,[],[f144,f86])).
% 0.22/0.45  fof(f86,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_setfam_1(X1,k4_enumset1(X0,X0,X0,X0,X0,X0)) | r1_tarski(k3_tarski(X1),X0)) )),
% 0.22/0.45    inference(superposition,[],[f32,f45])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,axiom,(
% 0.22/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.22/0.45  fof(f144,plain,(
% 0.22/0.45    r1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_14),
% 0.22/0.45    inference(avatar_component_clause,[],[f142])).
% 0.22/0.45  fof(f197,plain,(
% 0.22/0.45    spl3_14 | ~spl3_3 | ~spl3_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f194,f100,f59,f142])).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    spl3_3 <=> r1_setfam_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    spl3_9 <=> r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.45  fof(f194,plain,(
% 0.22/0.45    r1_setfam_1(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | (~spl3_3 | ~spl3_9)),
% 0.22/0.45    inference(resolution,[],[f137,f102])).
% 0.22/0.45  fof(f102,plain,(
% 0.22/0.45    r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) | ~spl3_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f100])).
% 0.22/0.45  fof(f137,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_setfam_1(X0,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ) | ~spl3_3),
% 0.22/0.45    inference(resolution,[],[f76,f61])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    r1_setfam_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f59])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    ( ! [X2,X3,X1] : (~r1_setfam_1(X1,X2) | r1_setfam_1(X3,X2) | ~r1_tarski(X3,X1)) )),
% 0.22/0.45    inference(resolution,[],[f36,f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r1_setfam_1(X1,X2) | r1_setfam_1(X0,X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_setfam_1(X0,X2) | ~r1_setfam_1(X1,X2) | ~r1_setfam_1(X0,X1))),
% 0.22/0.45    inference(flattening,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_setfam_1(X0,X2) | (~r1_setfam_1(X1,X2) | ~r1_setfam_1(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : ((r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => r1_setfam_1(X0,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_setfam_1)).
% 0.22/0.45  fof(f103,plain,(
% 0.22/0.45    spl3_9 | ~spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f98,f54,f100])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    spl3_2 <=> r2_hidden(sK2,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    r1_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2),sK1) | ~spl3_2),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f56,f46])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f34,f43])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f27,f41])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.45    inference(nnf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    r2_hidden(sK2,sK1) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f54])).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f44,f59])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    r1_setfam_1(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.22/0.45    inference(definition_unfolding,[],[f24,f43])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f21,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0))) => (? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) => (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.22/0.45    inference(negated_conjecture,[],[f12])).
% 0.22/0.45  fof(f12,conjecture,(
% 0.22/0.45    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).
% 0.22/0.45  fof(f57,plain,(
% 0.22/0.45    spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f25,f54])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    r2_hidden(sK2,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    ~spl3_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f26,f49])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ~r1_tarski(sK2,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (15133)------------------------------
% 0.22/0.45  % (15133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (15133)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (15133)Memory used [KB]: 6140
% 0.22/0.45  % (15133)Time elapsed: 0.038 s
% 0.22/0.45  % (15133)------------------------------
% 0.22/0.45  % (15133)------------------------------
% 0.22/0.45  % (15125)Success in time 0.09 s
%------------------------------------------------------------------------------
