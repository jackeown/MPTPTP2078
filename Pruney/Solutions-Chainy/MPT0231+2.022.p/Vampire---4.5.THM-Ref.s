%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 299 expanded)
%              Number of leaves         :    9 (  87 expanded)
%              Depth                    :   17
%              Number of atoms          :  129 ( 552 expanded)
%              Number of equality atoms :   76 ( 384 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(subsumption_resolution,[],[f117,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f20,f17])).

fof(f17,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f117,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f58,f114])).

fof(f114,plain,(
    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f112,f107])).

fof(f107,plain,(
    sK0 != sK1 ),
    inference(superposition,[],[f16,f102])).

fof(f102,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f98,f63])).

fof(f98,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | sK1 = sK2 ),
    inference(superposition,[],[f58,f93])).

fof(f93,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f92,f16])).

fof(f92,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | sK0 = sK2
    | sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | sK0 = sK2
    | sK1 = sK2
    | sK0 = sK2 ),
    inference(resolution,[],[f87,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f87,plain,
    ( r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f58,f80])).

fof(f80,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(resolution,[],[f42,f39])).

fof(f39,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f15,f37,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f37])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f36])).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f15,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f23,f38,f38])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f16,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f112,plain,
    ( sK0 = sK1
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(resolution,[],[f106,f56])).

fof(f56,plain,(
    ! [X4,X2,X0] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X4,X2)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X4,X2) != X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f106,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
      | sK1 = X1
      | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ) ),
    inference(backward_demodulation,[],[f90,f102])).

fof(f90,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
      | sK2 = X1
      | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
      | sK2 = X1
      | sK2 = X1
      | sK2 = X1
      | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ) ),
    inference(superposition,[],[f59,f80])).

fof(f58,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:10:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (17929)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.50  % (17937)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.50  % (17928)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (17920)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (17929)Refutation not found, incomplete strategy% (17929)------------------------------
% 0.22/0.51  % (17929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17929)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17929)Memory used [KB]: 6140
% 0.22/0.51  % (17929)Time elapsed: 0.054 s
% 0.22/0.51  % (17929)------------------------------
% 0.22/0.51  % (17929)------------------------------
% 0.22/0.51  % (17921)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (17920)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f117,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f20,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    r2_hidden(sK0,k1_xboole_0)),
% 0.22/0.51    inference(superposition,[],[f58,f114])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f112,f107])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    sK0 != sK1),
% 0.22/0.51    inference(superposition,[],[f16,f102])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    sK1 = sK2),
% 0.22/0.51    inference(subsumption_resolution,[],[f98,f63])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    r2_hidden(sK0,k1_xboole_0) | sK1 = sK2),
% 0.22/0.51    inference(superposition,[],[f58,f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | sK1 = sK2),
% 0.22/0.51    inference(subsumption_resolution,[],[f92,f16])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | sK0 = sK2 | sK1 = sK2),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) | sK0 = sK2 | sK1 = sK2 | sK0 = sK2),
% 0.22/0.51    inference(resolution,[],[f87,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.22/0.51    inference(equality_resolution,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.22/0.51    inference(definition_unfolding,[],[f32,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f26,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    r2_hidden(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.22/0.51    inference(superposition,[],[f58,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    k3_enumset1(sK0,sK0,sK0,sK0,sK1) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f42,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.22/0.51    inference(definition_unfolding,[],[f15,f37,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f18,f37])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f19,f36])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(definition_unfolding,[],[f23,f38,f38])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    sK0 != sK2),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    sK0 = sK1 | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f106,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X4,X2,X0] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X4,X2))) )),
% 0.22/0.51    inference(equality_resolution,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X4,X2) != X3) )),
% 0.22/0.51    inference(equality_resolution,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.22/0.51    inference(definition_unfolding,[],[f34,f36])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK1 = X1 | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)) )),
% 0.22/0.51    inference(backward_demodulation,[],[f90,f102])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK2 = X1 | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK2 = X1 | sK2 = X1 | sK2 = X1 | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)) )),
% 0.22/0.51    inference(superposition,[],[f59,f80])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 0.22/0.51    inference(equality_resolution,[],[f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 0.22/0.51    inference(equality_resolution,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.22/0.51    inference(definition_unfolding,[],[f33,f36])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (17920)------------------------------
% 0.22/0.51  % (17920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17920)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (17920)Memory used [KB]: 6268
% 0.22/0.51  % (17920)Time elapsed: 0.100 s
% 0.22/0.51  % (17920)------------------------------
% 0.22/0.51  % (17920)------------------------------
% 0.22/0.51  % (17913)Success in time 0.141 s
%------------------------------------------------------------------------------
