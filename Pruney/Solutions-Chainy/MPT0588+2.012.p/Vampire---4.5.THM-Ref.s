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
% DateTime   : Thu Dec  3 12:50:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 152 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 262 expanded)
%              Number of equality atoms :   36 ( 110 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f97,f113,f139,f147,f162])).

fof(f162,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f159,f23])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f159,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_9 ),
    inference(resolution,[],[f146,f79])).

fof(f79,plain,(
    ! [X6,X7] :
      ( r1_tarski(k7_relat_1(X6,X7),X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f39,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(X0,k2_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f146,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),sK1)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl2_9
  <=> r1_tarski(k7_relat_1(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f147,plain,
    ( ~ spl2_6
    | ~ spl2_1
    | ~ spl2_9
    | spl2_7 ),
    inference(avatar_split_clause,[],[f141,f110,f144,f55,f106])).

fof(f106,plain,
    ( spl2_6
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f55,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f110,plain,
    ( spl2_7
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f141,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_7 ),
    inference(resolution,[],[f112,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f112,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f139,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f135,f23])).

fof(f135,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_6 ),
    inference(resolution,[],[f108,f80])).

fof(f80,plain,(
    ! [X4,X5] :
      ( v1_relat_1(k7_relat_1(X4,X5))
      | ~ v1_relat_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X4,X5] :
      ( v1_relat_1(k7_relat_1(X4,X5))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f41,f42])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f108,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f113,plain,
    ( ~ spl2_6
    | ~ spl2_7
    | spl2_5 ),
    inference(avatar_split_clause,[],[f104,f94,f110,f106])).

fof(f94,plain,
    ( spl2_5
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f104,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_5 ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_5 ),
    inference(superposition,[],[f96,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f96,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f97,plain,
    ( ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f89,f94,f55])).

fof(f89,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f50,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f50,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f38,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f28,f36,f36])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f38,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f24,f37])).

fof(f24,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f57,f23])).

fof(f57,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (4860)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (4860)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f68,f97,f113,f139,f147,f162])).
% 0.21/0.44  fof(f162,plain,(
% 0.21/0.44    spl2_9),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.44  fof(f161,plain,(
% 0.21/0.44    $false | spl2_9),
% 0.21/0.44    inference(resolution,[],[f159,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.44    inference(negated_conjecture,[],[f11])).
% 0.21/0.44  fof(f11,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 0.21/0.44  fof(f159,plain,(
% 0.21/0.44    ~v1_relat_1(sK1) | spl2_9),
% 0.21/0.44    inference(resolution,[],[f146,f79])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X6,X7] : (r1_tarski(k7_relat_1(X6,X7),X6) | ~v1_relat_1(X6)) )),
% 0.21/0.44    inference(superposition,[],[f39,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f32,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f30,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f29,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f27,f37])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.44  fof(f146,plain,(
% 0.21/0.44    ~r1_tarski(k7_relat_1(sK1,sK0),sK1) | spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f144])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    spl2_9 <=> r1_tarski(k7_relat_1(sK1,sK0),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    ~spl2_6 | ~spl2_1 | ~spl2_9 | spl2_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f141,f110,f144,f55,f106])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    spl2_6 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    spl2_7 <=> r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    ~r1_tarski(k7_relat_1(sK1,sK0),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_7),
% 0.21/0.44    inference(resolution,[],[f112,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) | spl2_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f110])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    spl2_6),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f138])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    $false | spl2_6),
% 0.21/0.44    inference(resolution,[],[f135,f23])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    ~v1_relat_1(sK1) | spl2_6),
% 0.21/0.44    inference(resolution,[],[f108,f80])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X4,X5] : (v1_relat_1(k7_relat_1(X4,X5)) | ~v1_relat_1(X4)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X4,X5] : (v1_relat_1(k7_relat_1(X4,X5)) | ~v1_relat_1(X4) | ~v1_relat_1(X4)) )),
% 0.21/0.44    inference(superposition,[],[f41,f42])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f31,f37])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f106])).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    ~spl2_6 | ~spl2_7 | spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f104,f94,f110,f106])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    spl2_5 <=> k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f104,plain,(
% 0.21/0.44    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_5),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f103])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) | ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(sK1)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_5),
% 0.21/0.44    inference(superposition,[],[f96,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) | spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f94])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    ~spl2_1 | ~spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f89,f94,f55])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.44    inference(superposition,[],[f50,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f35,f37])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1))))),
% 0.21/0.44    inference(forward_demodulation,[],[f38,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f28,f36,f36])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))),
% 0.21/0.44    inference(definition_unfolding,[],[f24,f37])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl2_1),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    $false | spl2_1),
% 0.21/0.44    inference(resolution,[],[f57,f23])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ~v1_relat_1(sK1) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f55])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (4860)------------------------------
% 0.21/0.44  % (4860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (4860)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (4860)Memory used [KB]: 6140
% 0.21/0.44  % (4860)Time elapsed: 0.009 s
% 0.21/0.44  % (4860)------------------------------
% 0.21/0.44  % (4860)------------------------------
% 0.21/0.44  % (4851)Success in time 0.089 s
%------------------------------------------------------------------------------
