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
% DateTime   : Thu Dec  3 12:53:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 132 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 276 expanded)
%              Number of equality atoms :   51 ( 138 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f55,f72,f104,f118])).

fof(f118,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f117,f68,f52,f37])).

fof(f37,plain,
    ( spl3_2
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( spl3_7
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f117,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f111,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f111,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f105,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f105,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f100,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f100,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f94,f74])).

fof(f74,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4)) ),
    inference(superposition,[],[f29,f30])).

fof(f29,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f21,f28,f28])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f94,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f54,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(forward_demodulation,[],[f31,f30])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f54,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f104,plain,
    ( spl3_1
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f103,f68,f52,f33])).

fof(f33,plain,
    ( spl3_1
  <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f103,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f99,f20])).

fof(f99,plain,
    ( k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f94,f70])).

fof(f72,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f64,f42,f68])).

fof(f42,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f64,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f26,f44])).

fof(f44,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f52])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
      | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
    & r1_tarski(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
          | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
        | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) )
      & r1_tarski(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f37,f33])).

fof(f19,plain,
    ( k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0)
    | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (28851)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.44  % (28851)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f120,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f40,f45,f55,f72,f104,f118])).
% 0.22/0.44  fof(f118,plain,(
% 0.22/0.44    spl3_2 | ~spl3_5 | ~spl3_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f117,f68,f52,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    spl3_2 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl3_5 <=> v1_relat_1(sK2)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.44  fof(f68,plain,(
% 0.22/0.44    spl3_7 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.44  fof(f117,plain,(
% 0.22/0.44    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK1),sK0) | (~spl3_5 | ~spl3_7)),
% 0.22/0.44    inference(forward_demodulation,[],[f111,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.44  fof(f111,plain,(
% 0.22/0.44    k7_relat_1(k7_relat_1(sK2,sK1),sK0) = k7_relat_1(sK2,k4_xboole_0(sK0,k1_xboole_0)) | (~spl3_5 | ~spl3_7)),
% 0.22/0.44    inference(superposition,[],[f105,f70])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f68])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ) | ~spl3_5),
% 0.22/0.44    inference(forward_demodulation,[],[f100,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f23,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f22,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) ) | ~spl3_5),
% 0.22/0.45    inference(superposition,[],[f94,f74])).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k1_setfam_1(k2_enumset1(X5,X5,X5,X4))) )),
% 0.22/0.45    inference(superposition,[],[f29,f30])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f21,f28,f28])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.45  fof(f94,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_5),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f54,f85])).
% 0.22/0.45  fof(f85,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f31,f30])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f27,f28])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    v1_relat_1(sK2) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f52])).
% 0.22/0.45  fof(f104,plain,(
% 0.22/0.45    spl3_1 | ~spl3_5 | ~spl3_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f103,f68,f52,f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    spl3_1 <=> k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f103,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | (~spl3_5 | ~spl3_7)),
% 0.22/0.45    inference(forward_demodulation,[],[f99,f20])).
% 0.22/0.45  fof(f99,plain,(
% 0.22/0.45    k7_relat_1(k7_relat_1(sK2,sK0),sK1) = k7_relat_1(sK2,k4_xboole_0(sK0,k1_xboole_0)) | (~spl3_5 | ~spl3_7)),
% 0.22/0.45    inference(superposition,[],[f94,f70])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    spl3_7 | ~spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f64,f42,f68])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.45    inference(resolution,[],[f26,f44])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f42])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.45    inference(nnf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    spl3_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f16,f52])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    v1_relat_1(sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    (k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => ((k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ? [X0,X1,X2] : ((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (((k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0) | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1)) & r1_tarski(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.22/0.45    inference(negated_conjecture,[],[f8])).
% 0.22/0.45  fof(f8,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    spl3_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f18,f42])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    r1_tarski(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ~spl3_1 | ~spl3_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f19,f37,f33])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK1),sK0) | k7_relat_1(sK2,sK0) != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (28851)------------------------------
% 0.22/0.45  % (28851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (28851)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (28851)Memory used [KB]: 6140
% 0.22/0.45  % (28851)Time elapsed: 0.008 s
% 0.22/0.45  % (28851)------------------------------
% 0.22/0.45  % (28851)------------------------------
% 0.22/0.45  % (28844)Success in time 0.086 s
%------------------------------------------------------------------------------
