%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:13 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  86 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :   16
%              Number of atoms          :  106 ( 322 expanded)
%              Number of equality atoms :   38 ( 103 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(subsumption_resolution,[],[f66,f39])).

fof(f39,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f66,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(resolution,[],[f63,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f63,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f59,f41])).

fof(f41,plain,(
    r2_hidden(sK1,sK3) ),
    inference(subsumption_resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f23,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r2_hidden(sK1,sK3)
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) )
    & ( ( r2_hidden(sK1,sK3)
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(X1,X3)
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
        & ( ( r2_hidden(X1,X3)
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) )
   => ( ( ~ r2_hidden(sK1,sK3)
        | sK0 != sK2
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) )
      & ( ( r2_hidden(sK1,sK3)
          & sK0 = sK2 )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f59,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) ),
    inference(forward_demodulation,[],[f57,f55])).

fof(f55,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f54,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,
    ( sK0 = sK2
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(resolution,[],[f45,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | sK0 = sK2 ),
    inference(resolution,[],[f22,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))
    | sK0 = sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( sK0 != sK0
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(backward_demodulation,[],[f40,f55])).

fof(f40,plain,
    ( sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(subsumption_resolution,[],[f24,f34])).

fof(f24,plain,
    ( ~ r2_hidden(sK1,sK3)
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:21:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (5958)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (5960)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (5959)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (5976)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (5961)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (5980)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (5956)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.52  % (5955)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.52  % (5973)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.22/0.52  % (5977)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.22/0.53  % (5957)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.53  % (5980)Refutation found. Thanks to Tanya!
% 1.22/0.53  % SZS status Theorem for theBenchmark
% 1.22/0.53  % SZS output start Proof for theBenchmark
% 1.22/0.53  fof(f67,plain,(
% 1.22/0.53    $false),
% 1.22/0.53    inference(subsumption_resolution,[],[f66,f39])).
% 1.22/0.53  fof(f39,plain,(
% 1.22/0.53    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.22/0.53    inference(equality_resolution,[],[f29])).
% 1.22/0.53  fof(f29,plain,(
% 1.22/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f19])).
% 1.22/0.53  fof(f19,plain,(
% 1.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.22/0.53    inference(nnf_transformation,[],[f10])).
% 1.22/0.53  fof(f10,axiom,(
% 1.22/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.22/0.53  fof(f66,plain,(
% 1.22/0.53    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.22/0.53    inference(resolution,[],[f63,f28])).
% 1.22/0.53  fof(f28,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f18])).
% 1.22/0.53  fof(f18,plain,(
% 1.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.22/0.53    inference(nnf_transformation,[],[f8])).
% 1.22/0.53  fof(f8,axiom,(
% 1.22/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.22/0.53  fof(f63,plain,(
% 1.22/0.53    ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.22/0.53    inference(subsumption_resolution,[],[f59,f41])).
% 1.22/0.53  fof(f41,plain,(
% 1.22/0.53    r2_hidden(sK1,sK3)),
% 1.22/0.53    inference(subsumption_resolution,[],[f23,f34])).
% 1.22/0.53  fof(f34,plain,(
% 1.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f21])).
% 1.22/0.53  fof(f21,plain,(
% 1.22/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.22/0.53    inference(flattening,[],[f20])).
% 1.22/0.53  fof(f20,plain,(
% 1.22/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.22/0.53    inference(nnf_transformation,[],[f9])).
% 1.22/0.53  fof(f9,axiom,(
% 1.22/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.22/0.53  fof(f23,plain,(
% 1.22/0.53    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.22/0.53    inference(cnf_transformation,[],[f17])).
% 1.22/0.53  fof(f17,plain,(
% 1.22/0.53    (~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))) & ((r2_hidden(sK1,sK3) & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 1.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).
% 1.22/0.53  fof(f16,plain,(
% 1.22/0.53    ? [X0,X1,X2,X3] : ((~r2_hidden(X1,X3) | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)))) => ((~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))) & ((r2_hidden(sK1,sK3) & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))))),
% 1.22/0.53    introduced(choice_axiom,[])).
% 1.22/0.53  fof(f15,plain,(
% 1.22/0.53    ? [X0,X1,X2,X3] : ((~r2_hidden(X1,X3) | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.22/0.53    inference(flattening,[],[f14])).
% 1.22/0.53  fof(f14,plain,(
% 1.22/0.53    ? [X0,X1,X2,X3] : (((~r2_hidden(X1,X3) | X0 != X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.22/0.53    inference(nnf_transformation,[],[f13])).
% 1.22/0.53  fof(f13,plain,(
% 1.22/0.53    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <~> (r2_hidden(X1,X3) & X0 = X2))),
% 1.22/0.53    inference(ennf_transformation,[],[f12])).
% 1.22/0.53  fof(f12,negated_conjecture,(
% 1.22/0.53    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.22/0.53    inference(negated_conjecture,[],[f11])).
% 1.22/0.53  fof(f11,conjecture,(
% 1.22/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 1.22/0.53  fof(f59,plain,(
% 1.22/0.53    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK0,k1_tarski(sK0))),
% 1.22/0.53    inference(resolution,[],[f58,f35])).
% 1.22/0.53  fof(f35,plain,(
% 1.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f21])).
% 1.22/0.53  fof(f58,plain,(
% 1.22/0.53    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))),
% 1.22/0.53    inference(forward_demodulation,[],[f57,f55])).
% 1.22/0.53  fof(f55,plain,(
% 1.22/0.53    sK0 = sK2),
% 1.22/0.53    inference(subsumption_resolution,[],[f54,f30])).
% 1.22/0.53  fof(f30,plain,(
% 1.22/0.53    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.22/0.53    inference(cnf_transformation,[],[f19])).
% 1.22/0.53  fof(f54,plain,(
% 1.22/0.53    sK0 = sK2 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),
% 1.22/0.53    inference(resolution,[],[f45,f27])).
% 1.22/0.53  fof(f27,plain,(
% 1.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.22/0.53    inference(cnf_transformation,[],[f18])).
% 1.22/0.53  fof(f45,plain,(
% 1.22/0.53    r2_hidden(sK0,k1_tarski(sK2)) | sK0 = sK2),
% 1.22/0.53    inference(resolution,[],[f22,f33])).
% 1.22/0.53  fof(f33,plain,(
% 1.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.22/0.53    inference(cnf_transformation,[],[f21])).
% 1.22/0.53  fof(f22,plain,(
% 1.22/0.53    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) | sK0 = sK2),
% 1.22/0.53    inference(cnf_transformation,[],[f17])).
% 1.22/0.53  fof(f57,plain,(
% 1.22/0.53    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.22/0.53    inference(trivial_inequality_removal,[],[f56])).
% 1.22/0.53  fof(f56,plain,(
% 1.22/0.53    sK0 != sK0 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.22/0.53    inference(backward_demodulation,[],[f40,f55])).
% 1.22/0.53  fof(f40,plain,(
% 1.22/0.53    sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.22/0.53    inference(subsumption_resolution,[],[f24,f34])).
% 1.22/0.53  fof(f24,plain,(
% 1.22/0.53    ~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.22/0.53    inference(cnf_transformation,[],[f17])).
% 1.22/0.53  % SZS output end Proof for theBenchmark
% 1.22/0.53  % (5980)------------------------------
% 1.22/0.53  % (5980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (5980)Termination reason: Refutation
% 1.22/0.53  
% 1.22/0.53  % (5980)Memory used [KB]: 1791
% 1.22/0.53  % (5980)Time elapsed: 0.080 s
% 1.22/0.53  % (5980)------------------------------
% 1.22/0.53  % (5980)------------------------------
% 1.22/0.53  % (5957)Refutation not found, incomplete strategy% (5957)------------------------------
% 1.22/0.53  % (5957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (5957)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (5957)Memory used [KB]: 10746
% 1.22/0.53  % (5957)Time elapsed: 0.113 s
% 1.22/0.53  % (5957)------------------------------
% 1.22/0.53  % (5957)------------------------------
% 1.22/0.53  % (5965)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.22/0.53  % (5981)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.22/0.53  % (5970)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.22/0.53  % (5977)Refutation not found, incomplete strategy% (5977)------------------------------
% 1.22/0.53  % (5977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (5954)Success in time 0.18 s
%------------------------------------------------------------------------------
