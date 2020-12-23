%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:31 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 180 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   20
%              Number of atoms          :  171 ( 533 expanded)
%              Number of equality atoms :   18 (  37 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f816,plain,(
    $false ),
    inference(subsumption_resolution,[],[f815,f33])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f24])).

fof(f24,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f815,plain,(
    ~ r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f798,f103])).

fof(f103,plain,(
    ! [X6,X7] :
      ( r1_xboole_0(X7,X6)
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f39,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f798,plain,(
    ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f778,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f778,plain,(
    r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f747,f43])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f747,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK1) ),
    inference(resolution,[],[f704,f77])).

fof(f77,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(X8,k3_xboole_0(X7,X6))
      | ~ r1_xboole_0(X8,X6) ) ),
    inference(superposition,[],[f49,f36])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f704,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f689,f103])).

fof(f689,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f688,f36])).

fof(f688,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f680,f305])).

fof(f305,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f290,f103])).

fof(f290,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f289,f33])).

fof(f289,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f284])).

fof(f284,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f282,f61])).

fof(f61,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k3_xboole_0(X5,X4)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f45,f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f282,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f99,f115])).

fof(f115,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f103,f34])).

fof(f34,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,(
    ! [X21,X19,X20] :
      ( r1_xboole_0(X19,k2_xboole_0(X20,X21))
      | k1_xboole_0 != k3_xboole_0(X19,X21)
      | ~ r1_xboole_0(X19,X20) ) ),
    inference(superposition,[],[f46,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f680,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))
    | r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f476,f254])).

fof(f254,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f251])).

fof(f251,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f84,f87])).

fof(f87,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK4(X4,X5),k3_xboole_0(X5,X4))
      | r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f38,f36])).

fof(f84,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(sK4(X2,X3),X4)
      | ~ r1_xboole_0(X4,k3_xboole_0(X2,X3))
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f38,f42])).

fof(f476,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k3_xboole_0(sK0,sK1))
      | ~ r1_xboole_0(X0,k1_tarski(sK3)) ) ),
    inference(resolution,[],[f137,f31])).

fof(f31,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,(
    ! [X17,X15,X16] :
      ( ~ r1_tarski(X16,X15)
      | ~ r1_xboole_0(X17,X15)
      | r1_xboole_0(X17,X16) ) ),
    inference(superposition,[],[f49,f54])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:01:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.43  % (23503)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.44  % (23515)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.45  % (23506)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.45  % (23502)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (23504)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.46  % (23514)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.46  % (23503)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f816,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(subsumption_resolution,[],[f815,f33])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    r1_xboole_0(sK2,sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.19/0.46    inference(flattening,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.19/0.46    inference(ennf_transformation,[],[f13])).
% 0.19/0.46  fof(f13,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.19/0.46    inference(negated_conjecture,[],[f12])).
% 0.19/0.46  fof(f12,conjecture,(
% 0.19/0.46    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.19/0.46  fof(f815,plain,(
% 0.19/0.46    ~r1_xboole_0(sK2,sK1)),
% 0.19/0.46    inference(resolution,[],[f798,f103])).
% 0.19/0.46  fof(f103,plain,(
% 0.19/0.46    ( ! [X6,X7] : (r1_xboole_0(X7,X6) | ~r1_xboole_0(X6,X7)) )),
% 0.19/0.46    inference(resolution,[],[f50,f38])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.46    inference(rectify,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.46    inference(superposition,[],[f39,f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f27])).
% 0.19/0.46  fof(f798,plain,(
% 0.19/0.46    ~r1_xboole_0(sK1,sK2)),
% 0.19/0.46    inference(resolution,[],[f778,f79])).
% 0.19/0.46  fof(f79,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 0.19/0.46    inference(resolution,[],[f42,f32])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    r2_hidden(sK3,sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f25])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.46    inference(rectify,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.19/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.19/0.46  fof(f778,plain,(
% 0.19/0.46    r2_hidden(sK3,sK1)),
% 0.19/0.46    inference(resolution,[],[f747,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,axiom,(
% 0.19/0.47    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.19/0.47  fof(f747,plain,(
% 0.19/0.47    ~r1_xboole_0(k1_tarski(sK3),sK1)),
% 0.19/0.47    inference(resolution,[],[f704,f77])).
% 0.19/0.47  fof(f77,plain,(
% 0.19/0.47    ( ! [X6,X8,X7] : (r1_xboole_0(X8,k3_xboole_0(X7,X6)) | ~r1_xboole_0(X8,X6)) )),
% 0.19/0.47    inference(superposition,[],[f49,f36])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.19/0.47  fof(f704,plain,(
% 0.19/0.47    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))),
% 0.19/0.47    inference(resolution,[],[f689,f103])).
% 0.19/0.47  fof(f689,plain,(
% 0.19/0.47    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.19/0.47    inference(forward_demodulation,[],[f688,f36])).
% 0.19/0.47  fof(f688,plain,(
% 0.19/0.47    ~r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))),
% 0.19/0.47    inference(subsumption_resolution,[],[f680,f305])).
% 0.19/0.47  fof(f305,plain,(
% 0.19/0.47    ~r1_xboole_0(sK0,sK1)),
% 0.19/0.47    inference(resolution,[],[f290,f103])).
% 0.19/0.47  fof(f290,plain,(
% 0.19/0.47    ~r1_xboole_0(sK1,sK0)),
% 0.19/0.47    inference(subsumption_resolution,[],[f289,f33])).
% 0.19/0.47  fof(f289,plain,(
% 0.19/0.47    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK2,sK1)),
% 0.19/0.47    inference(trivial_inequality_removal,[],[f284])).
% 0.19/0.47  fof(f284,plain,(
% 0.19/0.47    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK2,sK1)),
% 0.19/0.47    inference(superposition,[],[f282,f61])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X5,X4) | ~r1_xboole_0(X4,X5)) )),
% 0.19/0.47    inference(superposition,[],[f45,f36])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.19/0.47    inference(nnf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.47  fof(f282,plain,(
% 0.19/0.47    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 0.19/0.47    inference(resolution,[],[f99,f115])).
% 0.19/0.47  fof(f115,plain,(
% 0.19/0.47    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.19/0.47    inference(resolution,[],[f103,f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f25])).
% 0.19/0.47  fof(f99,plain,(
% 0.19/0.47    ( ! [X21,X19,X20] : (r1_xboole_0(X19,k2_xboole_0(X20,X21)) | k1_xboole_0 != k3_xboole_0(X19,X21) | ~r1_xboole_0(X19,X20)) )),
% 0.19/0.47    inference(superposition,[],[f46,f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f30])).
% 0.19/0.47  fof(f680,plain,(
% 0.19/0.47    ~r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) | r1_xboole_0(sK0,sK1)),
% 0.19/0.47    inference(resolution,[],[f476,f254])).
% 0.19/0.47  fof(f254,plain,(
% 0.19/0.47    ( ! [X2,X3] : (~r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X3,X2)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f251])).
% 0.19/0.47  fof(f251,plain,(
% 0.19/0.47    ( ! [X2,X3] : (~r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.19/0.47    inference(resolution,[],[f84,f87])).
% 0.19/0.47  fof(f87,plain,(
% 0.19/0.47    ( ! [X4,X5] : (r2_hidden(sK4(X4,X5),k3_xboole_0(X5,X4)) | r1_xboole_0(X4,X5)) )),
% 0.19/0.47    inference(superposition,[],[f38,f36])).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    ( ! [X4,X2,X3] : (~r2_hidden(sK4(X2,X3),X4) | ~r1_xboole_0(X4,k3_xboole_0(X2,X3)) | r1_xboole_0(X2,X3)) )),
% 0.19/0.47    inference(resolution,[],[f38,f42])).
% 0.19/0.47  fof(f476,plain,(
% 0.19/0.47    ( ! [X0] : (r1_xboole_0(X0,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(X0,k1_tarski(sK3))) )),
% 0.19/0.47    inference(resolution,[],[f137,f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.19/0.47    inference(cnf_transformation,[],[f25])).
% 0.19/0.47  fof(f137,plain,(
% 0.19/0.47    ( ! [X17,X15,X16] : (~r1_tarski(X16,X15) | ~r1_xboole_0(X17,X15) | r1_xboole_0(X17,X16)) )),
% 0.19/0.47    inference(superposition,[],[f49,f54])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 0.19/0.47    inference(superposition,[],[f44,f36])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (23503)------------------------------
% 0.19/0.47  % (23503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (23503)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (23503)Memory used [KB]: 1918
% 0.19/0.47  % (23503)Time elapsed: 0.039 s
% 0.19/0.47  % (23503)------------------------------
% 0.19/0.47  % (23503)------------------------------
% 0.19/0.47  % (23492)Success in time 0.12 s
%------------------------------------------------------------------------------
