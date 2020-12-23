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
% DateTime   : Thu Dec  3 12:43:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 136 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :   17
%              Number of atoms          :  173 ( 429 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f518,plain,(
    $false ),
    inference(resolution,[],[f501,f33])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f501,plain,(
    ! [X0] : ~ r1_xboole_0(sK2,X0) ),
    inference(subsumption_resolution,[],[f497,f33])).

fof(f497,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK2,sK1)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f477,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(sK3),X0)
      | ~ r1_xboole_0(sK2,X0)
      | ~ r1_xboole_0(sK2,X1) ) ),
    inference(resolution,[],[f134,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(sK2,k2_xboole_0(X0,X1))
      | r1_xboole_0(k1_tarski(sK3),X0) ) ),
    inference(resolution,[],[f133,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f133,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(k2_xboole_0(X4,X5),sK2)
      | r1_xboole_0(k1_tarski(sK3),X4) ) ),
    inference(resolution,[],[f64,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f64,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,k2_xboole_0(X4,X5))
      | r1_xboole_0(k1_tarski(X3),X4) ) ),
    inference(resolution,[],[f48,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f477,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK1) ),
    inference(resolution,[],[f389,f68])).

fof(f68,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(X5,k3_xboole_0(X4,X3))
      | ~ r1_xboole_0(X5,X3) ) ),
    inference(superposition,[],[f50,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f389,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f380,f45])).

fof(f380,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f379,f36])).

fof(f379,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f367,f99])).

fof(f99,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f95,f45])).

fof(f95,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f94,f33])).

fof(f94,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f93,f45])).

fof(f93,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f47,f51])).

fof(f51,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f45,f34])).

fof(f34,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f367,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) ),
    inference(resolution,[],[f173,f276])).

fof(f276,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k3_xboole_0(sK0,sK1))
      | ~ r1_xboole_0(X0,k1_tarski(sK3)) ) ),
    inference(resolution,[],[f109,f31])).

fof(f31,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f109,plain,(
    ! [X12,X13,X11] :
      ( ~ r1_tarski(X12,X11)
      | ~ r1_xboole_0(X13,X11)
      | r1_xboole_0(X13,X12) ) ),
    inference(superposition,[],[f50,f57])).

fof(f57,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f44,f36])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f173,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f81,f83])).

fof(f83,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f38,f36])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f81,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK4(X4,X5),X6)
      | ~ r1_xboole_0(X6,k3_xboole_0(X4,X5))
      | r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f38,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:34:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (24864)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (24857)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (24866)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (24860)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (24857)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f518,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(resolution,[],[f501,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    r1_xboole_0(sK2,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.22/0.48  fof(f501,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_xboole_0(sK2,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f497,f33])).
% 0.22/0.48  fof(f497,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_xboole_0(sK2,sK1) | ~r1_xboole_0(sK2,X0)) )),
% 0.22/0.48    inference(resolution,[],[f477,f145])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(sK3),X0) | ~r1_xboole_0(sK2,X0) | ~r1_xboole_0(sK2,X1)) )),
% 0.22/0.48    inference(resolution,[],[f134,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_xboole_0(sK2,k2_xboole_0(X0,X1)) | r1_xboole_0(k1_tarski(sK3),X0)) )),
% 0.22/0.48    inference(resolution,[],[f133,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    ( ! [X4,X5] : (~r1_xboole_0(k2_xboole_0(X4,X5),sK2) | r1_xboole_0(k1_tarski(sK3),X4)) )),
% 0.22/0.48    inference(resolution,[],[f64,f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 0.22/0.48    inference(resolution,[],[f42,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    r2_hidden(sK3,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (r2_hidden(X3,k2_xboole_0(X4,X5)) | r1_xboole_0(k1_tarski(X3),X4)) )),
% 0.22/0.48    inference(resolution,[],[f48,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f477,plain,(
% 0.22/0.48    ~r1_xboole_0(k1_tarski(sK3),sK1)),
% 0.22/0.48    inference(resolution,[],[f389,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (r1_xboole_0(X5,k3_xboole_0(X4,X3)) | ~r1_xboole_0(X5,X3)) )),
% 0.22/0.48    inference(superposition,[],[f50,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.22/0.48  fof(f389,plain,(
% 0.22/0.48    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))),
% 0.22/0.48    inference(resolution,[],[f380,f45])).
% 0.22/0.48  fof(f380,plain,(
% 0.22/0.48    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.48    inference(forward_demodulation,[],[f379,f36])).
% 0.22/0.48  fof(f379,plain,(
% 0.22/0.48    ~r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))),
% 0.22/0.48    inference(subsumption_resolution,[],[f367,f99])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ~r1_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f95,f45])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f94,f33])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK2,sK1)),
% 0.22/0.48    inference(resolution,[],[f93,f45])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f47,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.22/0.48    inference(resolution,[],[f45,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f367,plain,(
% 0.22/0.48    r1_xboole_0(sK0,sK1) | ~r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))),
% 0.22/0.48    inference(resolution,[],[f173,f276])).
% 0.22/0.48  fof(f276,plain,(
% 0.22/0.48    ( ! [X0] : (r1_xboole_0(X0,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(X0,k1_tarski(sK3))) )),
% 0.22/0.48    inference(resolution,[],[f109,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ( ! [X12,X13,X11] : (~r1_tarski(X12,X11) | ~r1_xboole_0(X13,X11) | r1_xboole_0(X13,X12)) )),
% 0.22/0.48    inference(superposition,[],[f50,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.22/0.48    inference(superposition,[],[f44,f36])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X3,X2)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f168])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.22/0.48    inference(resolution,[],[f81,f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X2,X3] : (r2_hidden(sK4(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X2,X3)) )),
% 0.22/0.48    inference(superposition,[],[f38,f36])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ( ! [X6,X4,X5] : (~r2_hidden(sK4(X4,X5),X6) | ~r1_xboole_0(X6,k3_xboole_0(X4,X5)) | r1_xboole_0(X4,X5)) )),
% 0.22/0.48    inference(resolution,[],[f38,f42])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (24857)------------------------------
% 0.22/0.48  % (24857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (24857)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (24857)Memory used [KB]: 1791
% 0.22/0.48  % (24857)Time elapsed: 0.054 s
% 0.22/0.48  % (24857)------------------------------
% 0.22/0.48  % (24857)------------------------------
% 0.22/0.48  % (24865)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (24853)Success in time 0.118 s
%------------------------------------------------------------------------------
