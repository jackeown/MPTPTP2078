%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 180 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  125 ( 595 expanded)
%              Number of equality atoms :   48 ( 287 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f263,plain,(
    $false ),
    inference(subsumption_resolution,[],[f262,f27])).

fof(f27,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f21])).

% (21365)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (21362)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f21,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & sK0 != k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK1 = X2
          | ~ r2_hidden(X2,sK0) )
      & k1_xboole_0 != sK0
      & sK0 != k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f262,plain,(
    sK0 = k1_tarski(sK1) ),
    inference(backward_demodulation,[],[f51,f256])).

fof(f256,plain,(
    sK0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f226,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f226,plain,(
    ! [X4] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X4,k1_tarski(sK1))) ),
    inference(resolution,[],[f221,f122])).

fof(f122,plain,(
    ! [X0] : ~ r2_hidden(sK1,k4_xboole_0(X0,k1_tarski(sK1))) ),
    inference(resolution,[],[f98,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f98,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,k1_tarski(sK1))
      | ~ r2_hidden(sK1,X1) ) ),
    inference(resolution,[],[f88,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f88,plain,(
    r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f56,f82])).

fof(f82,plain,(
    sK1 = sK3(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f57,f29])).

fof(f29,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    r2_hidden(sK3(k1_tarski(sK1),sK0),sK0) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f48,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f47,f28])).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f31,f46])).

fof(f46,plain,(
    sK1 = sK2(sK0) ),
    inference(subsumption_resolution,[],[f43,f28])).

fof(f43,plain,
    ( sK1 = sK2(sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f29,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f56,plain,(
    r2_hidden(sK3(k1_tarski(sK1),sK0),k1_tarski(sK1)) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f221,plain,(
    ! [X1] :
      ( r2_hidden(sK1,X1)
      | sK0 = k4_xboole_0(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f220,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f220,plain,(
    ! [X1] :
      ( r2_hidden(sK1,X1)
      | r1_xboole_0(sK0,X1)
      | sK0 = k4_xboole_0(sK0,X1) ) ),
    inference(superposition,[],[f36,f134])).

fof(f134,plain,(
    ! [X0] :
      ( sK1 = sK3(sK0,X0)
      | sK0 = k4_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f45,f40])).

fof(f45,plain,(
    ! [X1] :
      ( r1_xboole_0(sK0,X1)
      | sK1 = sK3(sK0,X1) ) ),
    inference(resolution,[],[f29,f35])).

fof(f51,plain,(
    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f48,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (21363)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (21364)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (21382)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (21375)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (21377)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (21384)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (21370)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (21368)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (21382)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f262,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    sK0 != k1_tarski(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  % (21365)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (21362)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    sK0 = k1_tarski(sK1)),
% 0.21/0.53    inference(backward_demodulation,[],[f51,f256])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    sK0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.53    inference(superposition,[],[f226,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    ( ! [X4] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X4,k1_tarski(sK1)))) )),
% 0.21/0.53    inference(resolution,[],[f221,f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(X0,k1_tarski(sK1)))) )),
% 0.21/0.53    inference(resolution,[],[f98,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_xboole_0(X1,k1_tarski(sK1)) | ~r2_hidden(sK1,X1)) )),
% 0.21/0.53    inference(resolution,[],[f88,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_tarski(sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f56,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    sK1 = sK3(k1_tarski(sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f57,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    r2_hidden(sK3(k1_tarski(sK1),sK0),sK0)),
% 0.21/0.53    inference(resolution,[],[f50,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ~r1_xboole_0(k1_tarski(sK1),sK0)),
% 0.21/0.53    inference(resolution,[],[f48,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f47,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(superposition,[],[f31,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    sK1 = sK2(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f43,f28])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    sK1 = sK2(sK0) | k1_xboole_0 = sK0),
% 0.21/0.53    inference(resolution,[],[f29,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    r2_hidden(sK3(k1_tarski(sK1),sK0),k1_tarski(sK1))),
% 0.21/0.53    inference(resolution,[],[f50,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK1,X1) | sK0 = k4_xboole_0(sK0,X1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f220,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK1,X1) | r1_xboole_0(sK0,X1) | sK0 = k4_xboole_0(sK0,X1)) )),
% 0.21/0.53    inference(superposition,[],[f36,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ( ! [X0] : (sK1 = sK3(sK0,X0) | sK0 = k4_xboole_0(sK0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f45,f40])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X1] : (r1_xboole_0(sK0,X1) | sK1 = sK3(sK0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f29,f35])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.53    inference(resolution,[],[f48,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (21382)------------------------------
% 0.21/0.53  % (21382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21382)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (21382)Memory used [KB]: 1791
% 0.21/0.53  % (21382)Time elapsed: 0.077 s
% 0.21/0.53  % (21382)------------------------------
% 0.21/0.53  % (21382)------------------------------
% 0.21/0.53  % (21358)Success in time 0.172 s
%------------------------------------------------------------------------------
