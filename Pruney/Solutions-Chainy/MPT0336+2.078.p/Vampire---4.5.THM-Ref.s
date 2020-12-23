%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:34 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 129 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  178 ( 420 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f868,plain,(
    $false ),
    inference(resolution,[],[f831,f36])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f27])).

fof(f27,plain,
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

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f831,plain,(
    ! [X0] : ~ r1_xboole_0(sK2,X0) ),
    inference(subsumption_resolution,[],[f827,f36])).

fof(f827,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK2,sK1)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f784,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(sK3),X0)
      | ~ r1_xboole_0(sK2,X0)
      | ~ r1_xboole_0(sK2,X1) ) ),
    inference(resolution,[],[f120,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(sK2,k2_xboole_0(X0,X1))
      | r1_xboole_0(k1_tarski(sK3),X0) ) ),
    inference(resolution,[],[f119,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f119,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(k2_xboole_0(X4,X5),sK2)
      | r1_xboole_0(k1_tarski(sK3),X4) ) ),
    inference(resolution,[],[f65,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f65,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,k2_xboole_0(X4,X5))
      | r1_xboole_0(k1_tarski(X3),X4) ) ),
    inference(resolution,[],[f53,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f784,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK1) ),
    inference(resolution,[],[f633,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X2,X0) ) ),
    inference(superposition,[],[f56,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f633,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f523,f48])).

fof(f523,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f522,f39])).

fof(f522,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f497,f99])).

fof(f99,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f98,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f97,f48])).

fof(f97,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f497,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3)) ),
    inference(resolution,[],[f218,f124])).

fof(f124,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_xboole_0(sK0,sK1),X0)
      | ~ r1_xboole_0(X0,k1_tarski(sK3)) ) ),
    inference(resolution,[],[f68,f34])).

fof(f34,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_xboole_0(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f55,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f218,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2))
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f87,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0))
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f42,f39])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f87,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK4(X4,X5),X6)
      | ~ r1_xboole_0(X6,k3_xboole_0(X4,X5))
      | r1_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f42,f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (1748)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (1747)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (1744)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (1737)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (1738)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.51  % (1743)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.51  % (1749)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (1750)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.52  % (1745)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.52  % (1733)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.52  % (1735)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.52  % (1742)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (1746)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.52  % (1741)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.53  % (1736)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.53  % (1739)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (1734)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.55  % (1740)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.87/0.61  % (1736)Refutation found. Thanks to Tanya!
% 1.87/0.61  % SZS status Theorem for theBenchmark
% 1.87/0.61  % SZS output start Proof for theBenchmark
% 1.87/0.61  fof(f868,plain,(
% 1.87/0.61    $false),
% 1.87/0.61    inference(resolution,[],[f831,f36])).
% 1.87/0.61  fof(f36,plain,(
% 1.87/0.61    r1_xboole_0(sK2,sK1)),
% 1.87/0.61    inference(cnf_transformation,[],[f28])).
% 1.87/0.61  fof(f28,plain,(
% 1.87/0.61    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f27])).
% 1.87/0.61  fof(f27,plain,(
% 1.87/0.61    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f19,plain,(
% 1.87/0.61    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.87/0.61    inference(flattening,[],[f18])).
% 1.87/0.61  fof(f18,plain,(
% 1.87/0.61    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.87/0.61    inference(ennf_transformation,[],[f15])).
% 1.87/0.61  fof(f15,negated_conjecture,(
% 1.87/0.61    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.87/0.61    inference(negated_conjecture,[],[f14])).
% 1.87/0.61  fof(f14,conjecture,(
% 1.87/0.61    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.87/0.61  fof(f831,plain,(
% 1.87/0.61    ( ! [X0] : (~r1_xboole_0(sK2,X0)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f827,f36])).
% 1.87/0.61  fof(f827,plain,(
% 1.87/0.61    ( ! [X0] : (~r1_xboole_0(sK2,sK1) | ~r1_xboole_0(sK2,X0)) )),
% 1.87/0.61    inference(resolution,[],[f784,f148])).
% 1.87/0.61  fof(f148,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(sK3),X0) | ~r1_xboole_0(sK2,X0) | ~r1_xboole_0(sK2,X1)) )),
% 1.87/0.61    inference(resolution,[],[f120,f52])).
% 1.87/0.61  fof(f52,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f24])).
% 1.87/0.61  fof(f24,plain,(
% 1.87/0.61    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.87/0.61    inference(ennf_transformation,[],[f6])).
% 1.87/0.61  fof(f6,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.87/0.61  fof(f120,plain,(
% 1.87/0.61    ( ! [X0,X1] : (~r1_xboole_0(sK2,k2_xboole_0(X0,X1)) | r1_xboole_0(k1_tarski(sK3),X0)) )),
% 1.87/0.61    inference(resolution,[],[f119,f48])).
% 1.87/0.61  fof(f48,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f23])).
% 1.87/0.61  fof(f23,plain,(
% 1.87/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.87/0.61    inference(ennf_transformation,[],[f2])).
% 1.87/0.61  fof(f2,axiom,(
% 1.87/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.87/0.61  fof(f119,plain,(
% 1.87/0.61    ( ! [X4,X5] : (~r1_xboole_0(k2_xboole_0(X4,X5),sK2) | r1_xboole_0(k1_tarski(sK3),X4)) )),
% 1.87/0.61    inference(resolution,[],[f65,f81])).
% 1.87/0.61  fof(f81,plain,(
% 1.87/0.61    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(X0,sK2)) )),
% 1.87/0.61    inference(resolution,[],[f46,f35])).
% 1.87/0.61  fof(f35,plain,(
% 1.87/0.61    r2_hidden(sK3,sK2)),
% 1.87/0.61    inference(cnf_transformation,[],[f28])).
% 1.87/0.61  fof(f46,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f32])).
% 1.87/0.61  fof(f32,plain,(
% 1.87/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f31])).
% 1.87/0.61  fof(f31,plain,(
% 1.87/0.61    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f21,plain,(
% 1.87/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(ennf_transformation,[],[f17])).
% 1.87/0.61  fof(f17,plain,(
% 1.87/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(rectify,[],[f3])).
% 1.87/0.61  fof(f3,axiom,(
% 1.87/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.87/0.61  fof(f65,plain,(
% 1.87/0.61    ( ! [X4,X5,X3] : (r2_hidden(X3,k2_xboole_0(X4,X5)) | r1_xboole_0(k1_tarski(X3),X4)) )),
% 1.87/0.61    inference(resolution,[],[f53,f47])).
% 1.87/0.61  fof(f47,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f22])).
% 1.87/0.61  fof(f22,plain,(
% 1.87/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.87/0.61    inference(ennf_transformation,[],[f13])).
% 1.87/0.61  fof(f13,axiom,(
% 1.87/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.87/0.61  fof(f53,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f24])).
% 1.87/0.61  fof(f784,plain,(
% 1.87/0.61    ~r1_xboole_0(k1_tarski(sK3),sK1)),
% 1.87/0.61    inference(resolution,[],[f633,f69])).
% 1.87/0.61  fof(f69,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X2,X0)) )),
% 1.87/0.61    inference(superposition,[],[f56,f39])).
% 1.87/0.61  fof(f39,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f1])).
% 1.87/0.61  fof(f1,axiom,(
% 1.87/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.87/0.61  fof(f56,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f26])).
% 1.87/0.61  fof(f26,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.87/0.61    inference(ennf_transformation,[],[f7])).
% 1.87/0.61  fof(f7,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.87/0.61  fof(f633,plain,(
% 1.87/0.61    ~r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,sK1))),
% 1.87/0.61    inference(resolution,[],[f523,f48])).
% 1.87/0.61  fof(f523,plain,(
% 1.87/0.61    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.87/0.61    inference(forward_demodulation,[],[f522,f39])).
% 1.87/0.61  fof(f522,plain,(
% 1.87/0.61    ~r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))),
% 1.87/0.61    inference(subsumption_resolution,[],[f497,f99])).
% 1.87/0.61  fof(f99,plain,(
% 1.87/0.61    ~r1_xboole_0(sK1,sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f98,f36])).
% 1.87/0.61  fof(f98,plain,(
% 1.87/0.61    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK2,sK1)),
% 1.87/0.61    inference(resolution,[],[f97,f48])).
% 1.87/0.61  fof(f97,plain,(
% 1.87/0.61    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 1.87/0.61    inference(resolution,[],[f52,f57])).
% 1.87/0.61  fof(f57,plain,(
% 1.87/0.61    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.87/0.61    inference(resolution,[],[f48,f37])).
% 1.87/0.61  fof(f37,plain,(
% 1.87/0.61    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.87/0.61    inference(cnf_transformation,[],[f28])).
% 1.87/0.61  fof(f497,plain,(
% 1.87/0.61    r1_xboole_0(sK1,sK0) | ~r1_xboole_0(k3_xboole_0(sK1,sK0),k1_tarski(sK3))),
% 1.87/0.61    inference(resolution,[],[f218,f124])).
% 1.87/0.61  fof(f124,plain,(
% 1.87/0.61    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X0) | ~r1_xboole_0(X0,k1_tarski(sK3))) )),
% 1.87/0.61    inference(resolution,[],[f68,f34])).
% 1.87/0.61  fof(f34,plain,(
% 1.87/0.61    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.87/0.61    inference(cnf_transformation,[],[f28])).
% 1.87/0.61  fof(f68,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_xboole_0(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(superposition,[],[f55,f49])).
% 1.87/0.61  fof(f49,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f33])).
% 1.87/0.61  fof(f33,plain,(
% 1.87/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(nnf_transformation,[],[f8])).
% 1.87/0.61  fof(f8,axiom,(
% 1.87/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.87/0.61  fof(f55,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f25])).
% 1.87/0.61  fof(f25,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.87/0.61    inference(ennf_transformation,[],[f9])).
% 1.87/0.61  fof(f9,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.87/0.61  fof(f218,plain,(
% 1.87/0.61    ( ! [X2,X3] : (~r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X3,X2)) )),
% 1.87/0.61    inference(duplicate_literal_removal,[],[f215])).
% 1.87/0.61  fof(f215,plain,(
% 1.87/0.61    ( ! [X2,X3] : (~r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X3,X2)) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 1.87/0.61    inference(resolution,[],[f87,f88])).
% 1.87/0.61  fof(f88,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(superposition,[],[f42,f39])).
% 1.87/0.61  fof(f42,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f30])).
% 1.87/0.61  fof(f30,plain,(
% 1.87/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f29])).
% 1.87/0.61  fof(f29,plain,(
% 1.87/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f20,plain,(
% 1.87/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(ennf_transformation,[],[f16])).
% 1.87/0.61  fof(f16,plain,(
% 1.87/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.87/0.61    inference(rectify,[],[f4])).
% 1.87/0.61  fof(f4,axiom,(
% 1.87/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.87/0.61  fof(f87,plain,(
% 1.87/0.61    ( ! [X6,X4,X5] : (~r2_hidden(sK4(X4,X5),X6) | ~r1_xboole_0(X6,k3_xboole_0(X4,X5)) | r1_xboole_0(X4,X5)) )),
% 1.87/0.61    inference(resolution,[],[f42,f46])).
% 1.87/0.61  % SZS output end Proof for theBenchmark
% 1.87/0.61  % (1736)------------------------------
% 1.87/0.61  % (1736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (1736)Termination reason: Refutation
% 1.87/0.61  
% 1.87/0.61  % (1736)Memory used [KB]: 2046
% 1.87/0.61  % (1736)Time elapsed: 0.176 s
% 1.87/0.61  % (1736)------------------------------
% 1.87/0.61  % (1736)------------------------------
% 1.87/0.61  % (1732)Success in time 0.251 s
%------------------------------------------------------------------------------
