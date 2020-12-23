%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 127 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 273 expanded)
%              Number of equality atoms :    8 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f63,f72])).

fof(f72,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f68,f19])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(f68,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_2 ),
    inference(resolution,[],[f66,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f66,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f65,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f64,f36])).

fof(f36,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k1_enumset1(X3,X3,X2)),X2) ),
    inference(superposition,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f24,f25,f25])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f64,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_2 ),
    inference(resolution,[],[f53,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f53,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_2
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f63,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f59,f19])).

fof(f59,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_1 ),
    inference(resolution,[],[f57,f33])).

fof(f57,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f56,f19])).

fof(f56,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f55,f31])).

fof(f55,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_1 ),
    inference(resolution,[],[f49,f22])).

fof(f49,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_1
  <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f54,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f45,f51,f47])).

fof(f45,plain,
    ( ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f30,plain,(
    ~ r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f21,f29,f29])).

fof(f21,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (5730)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.44  % (5730)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f54,f63,f72])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    $false | spl2_2),
% 0.21/0.44    inference(subsumption_resolution,[],[f68,f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    v1_relat_1(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f17,f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ~v1_relat_1(sK0) | spl2_2),
% 0.21/0.44    inference(resolution,[],[f66,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f27,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f26,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_2),
% 0.21/0.44    inference(subsumption_resolution,[],[f65,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_2),
% 0.21/0.44    inference(subsumption_resolution,[],[f64,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k1_enumset1(X3,X3,X2)),X2)) )),
% 0.21/0.44    inference(superposition,[],[f31,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f24,f25,f25])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f23,f29])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_2),
% 0.21/0.44    inference(resolution,[],[f53,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1)) | spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl2_2 <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl2_1),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    $false | spl2_1),
% 0.21/0.44    inference(subsumption_resolution,[],[f59,f19])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    ~v1_relat_1(sK0) | spl2_1),
% 0.21/0.44    inference(resolution,[],[f57,f33])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_1),
% 0.21/0.44    inference(subsumption_resolution,[],[f56,f19])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_1),
% 0.21/0.44    inference(subsumption_resolution,[],[f55,f31])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_1),
% 0.21/0.44    inference(resolution,[],[f49,f22])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0)) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl2_1 <=> r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ~spl2_1 | ~spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f45,f51,f47])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k3_relat_1(sK0))),
% 0.21/0.44    inference(resolution,[],[f30,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(definition_unfolding,[],[f28,f29])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k3_relat_1(sK0),k3_relat_1(sK0),k3_relat_1(sK1))))),
% 0.21/0.44    inference(definition_unfolding,[],[f21,f29,f29])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (5730)------------------------------
% 0.21/0.44  % (5730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (5730)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (5730)Memory used [KB]: 10618
% 0.21/0.44  % (5730)Time elapsed: 0.010 s
% 0.21/0.44  % (5730)------------------------------
% 0.21/0.44  % (5730)------------------------------
% 0.21/0.45  % (5720)Success in time 0.087 s
%------------------------------------------------------------------------------
