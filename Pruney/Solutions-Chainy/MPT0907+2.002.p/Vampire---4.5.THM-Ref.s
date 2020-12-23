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
% DateTime   : Thu Dec  3 12:59:21 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   36 (  69 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 216 expanded)
%              Number of equality atoms :   48 (  97 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(subsumption_resolution,[],[f45,f42])).

fof(f42,plain,(
    sK1 != k1_mcart_1(sK1) ),
    inference(superposition,[],[f31,f40])).

fof(f40,plain,(
    sK1 = k4_tarski(sK4(sK1,sK3,sK2),sK5(sK1,sK3,sK2)) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f13])).

% (10060)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f37,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X4,X5))
      | sK1 = k4_tarski(sK4(sK1,X5,X4),sK5(sK1,X5,X4)) ) ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( k4_tarski(X3,X4) = X0
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X2) )
     => ( k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( k4_tarski(X3,X4) = X0
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ sP0(X3,X2,X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ sP0(X3,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP0(sK1,X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X1,X0)) ) ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( sP0(X3,X2,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(definition_folding,[],[f8,f9])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f19,plain,(
    r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( sK1 = k2_mcart_1(sK1)
      | sK1 = k1_mcart_1(sK1) )
    & r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( sK1 = k2_mcart_1(sK1)
        | sK1 = k1_mcart_1(sK1) )
      & r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

fof(f31,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f45,plain,(
    sK1 = k1_mcart_1(sK1) ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( sK1 != sK1
    | sK1 = k1_mcart_1(sK1) ),
    inference(superposition,[],[f43,f20])).

fof(f20,plain,
    ( sK1 = k2_mcart_1(sK1)
    | sK1 = k1_mcart_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    sK1 != k2_mcart_1(sK1) ),
    inference(superposition,[],[f30,f40])).

fof(f30,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:46:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.46/0.57  % (10062)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.46/0.58  % (10078)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.46/0.58  % (10072)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.65/0.58  % (10065)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.65/0.58  % (10070)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.65/0.58  % (10057)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.65/0.58  % (10062)Refutation found. Thanks to Tanya!
% 1.65/0.58  % SZS status Theorem for theBenchmark
% 1.65/0.58  % SZS output start Proof for theBenchmark
% 1.65/0.58  fof(f46,plain,(
% 1.65/0.58    $false),
% 1.65/0.58    inference(subsumption_resolution,[],[f45,f42])).
% 1.65/0.58  fof(f42,plain,(
% 1.65/0.58    sK1 != k1_mcart_1(sK1)),
% 1.65/0.58    inference(superposition,[],[f31,f40])).
% 1.65/0.58  fof(f40,plain,(
% 1.65/0.58    sK1 = k4_tarski(sK4(sK1,sK3,sK2),sK5(sK1,sK3,sK2))),
% 1.65/0.58    inference(resolution,[],[f37,f33])).
% 1.65/0.58  fof(f33,plain,(
% 1.65/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.65/0.58    inference(equality_resolution,[],[f23])).
% 1.65/0.58  fof(f23,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f14])).
% 1.65/0.58  fof(f14,plain,(
% 1.65/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.58    inference(flattening,[],[f13])).
% 1.65/0.58  % (10060)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.65/0.58  fof(f13,plain,(
% 1.65/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.58    inference(nnf_transformation,[],[f1])).
% 1.65/0.58  fof(f1,axiom,(
% 1.65/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.65/0.58  fof(f37,plain,(
% 1.65/0.58    ( ! [X4,X5] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X4,X5)) | sK1 = k4_tarski(sK4(sK1,X5,X4),sK5(sK1,X5,X4))) )),
% 1.65/0.58    inference(resolution,[],[f34,f28])).
% 1.65/0.58  fof(f28,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f18])).
% 1.65/0.59  fof(f18,plain,(
% 1.65/0.59    ! [X0,X1,X2] : ((k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0 & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X2)) | ~sP0(X0,X1,X2))),
% 1.65/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f17])).
% 1.65/0.59  fof(f17,plain,(
% 1.65/0.59    ! [X2,X1,X0] : (? [X3,X4] : (k4_tarski(X3,X4) = X0 & r2_hidden(X4,X1) & r2_hidden(X3,X2)) => (k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)) = X0 & r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X2)))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f16,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (? [X3,X4] : (k4_tarski(X3,X4) = X0 & r2_hidden(X4,X1) & r2_hidden(X3,X2)) | ~sP0(X0,X1,X2))),
% 1.65/0.59    inference(rectify,[],[f15])).
% 1.65/0.59  fof(f15,plain,(
% 1.65/0.59    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~sP0(X3,X2,X1))),
% 1.65/0.59    inference(nnf_transformation,[],[f9])).
% 1.65/0.59  fof(f9,plain,(
% 1.65/0.59    ! [X3,X2,X1] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~sP0(X3,X2,X1))),
% 1.65/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.65/0.59  fof(f34,plain,(
% 1.65/0.59    ( ! [X0,X1] : (sP0(sK1,X0,X1) | ~r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X1,X0))) )),
% 1.65/0.59    inference(resolution,[],[f19,f29])).
% 1.65/0.59  fof(f29,plain,(
% 1.65/0.59    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f10])).
% 1.65/0.59  fof(f10,plain,(
% 1.65/0.59    ! [X0,X1,X2,X3] : (sP0(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.65/0.59    inference(definition_folding,[],[f8,f9])).
% 1.65/0.59  fof(f8,plain,(
% 1.65/0.59    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.65/0.59    inference(ennf_transformation,[],[f2])).
% 1.65/0.59  fof(f2,axiom,(
% 1.65/0.59    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 1.65/0.59  fof(f19,plain,(
% 1.65/0.59    r2_hidden(sK1,k2_zfmisc_1(sK2,sK3))),
% 1.65/0.59    inference(cnf_transformation,[],[f12])).
% 1.65/0.59  fof(f12,plain,(
% 1.65/0.59    (sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & r2_hidden(sK1,k2_zfmisc_1(sK2,sK3))),
% 1.65/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f11])).
% 1.65/0.59  fof(f11,plain,(
% 1.65/0.59    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => ((sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)) & r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f6,plain,(
% 1.65/0.59    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.65/0.59    inference(ennf_transformation,[],[f5])).
% 1.65/0.59  fof(f5,negated_conjecture,(
% 1.65/0.59    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.65/0.59    inference(negated_conjecture,[],[f4])).
% 1.65/0.59  fof(f4,conjecture,(
% 1.65/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).
% 1.65/0.59  fof(f31,plain,(
% 1.65/0.59    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 1.65/0.59    inference(equality_resolution,[],[f21])).
% 1.65/0.59  fof(f21,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (k1_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.65/0.59    inference(cnf_transformation,[],[f7])).
% 1.65/0.59  fof(f7,plain,(
% 1.65/0.59    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.65/0.59    inference(ennf_transformation,[],[f3])).
% 1.65/0.59  fof(f3,axiom,(
% 1.65/0.59    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.65/0.59  fof(f45,plain,(
% 1.65/0.59    sK1 = k1_mcart_1(sK1)),
% 1.65/0.59    inference(trivial_inequality_removal,[],[f44])).
% 1.65/0.59  fof(f44,plain,(
% 1.65/0.59    sK1 != sK1 | sK1 = k1_mcart_1(sK1)),
% 1.65/0.59    inference(superposition,[],[f43,f20])).
% 1.65/0.59  fof(f20,plain,(
% 1.65/0.59    sK1 = k2_mcart_1(sK1) | sK1 = k1_mcart_1(sK1)),
% 1.65/0.59    inference(cnf_transformation,[],[f12])).
% 1.65/0.59  fof(f43,plain,(
% 1.65/0.59    sK1 != k2_mcart_1(sK1)),
% 1.65/0.59    inference(superposition,[],[f30,f40])).
% 1.65/0.59  fof(f30,plain,(
% 1.65/0.59    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.65/0.59    inference(equality_resolution,[],[f22])).
% 1.65/0.59  fof(f22,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 1.65/0.59    inference(cnf_transformation,[],[f7])).
% 1.65/0.59  % SZS output end Proof for theBenchmark
% 1.65/0.59  % (10062)------------------------------
% 1.65/0.59  % (10062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (10062)Termination reason: Refutation
% 1.65/0.59  
% 1.65/0.59  % (10062)Memory used [KB]: 1663
% 1.65/0.59  % (10062)Time elapsed: 0.141 s
% 1.65/0.59  % (10062)------------------------------
% 1.65/0.59  % (10062)------------------------------
% 1.65/0.59  % (10066)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.65/0.59  % (10060)Refutation not found, incomplete strategy% (10060)------------------------------
% 1.65/0.59  % (10060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (10053)Success in time 0.216 s
%------------------------------------------------------------------------------
