%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:24 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  58 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 111 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f73,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] : r1_xboole_0(k10_relat_1(k1_xboole_0,X1),X0) ),
    inference(subsumption_resolution,[],[f71,f57])).

fof(f57,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f56,f42])).

% (3398)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_xboole_0,X0)
      | r1_xboole_0(k10_relat_1(k1_xboole_0,X1),X0) ) ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f70,plain,(
    ! [X2] : r1_tarski(k10_relat_1(k1_xboole_0,X2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f69,f63])).

fof(f63,plain,(
    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f62,f34])).

fof(f34,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f62,plain,(
    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f61,f35])).

fof(f35,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f40,f54])).

fof(f54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f69,plain,(
    ! [X2] : r1_tarski(k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f67,f35])).

fof(f67,plain,(
    ! [X2] : r1_tarski(k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f45,f54])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(f32,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f28])).

fof(f28,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (3386)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.49  % (3394)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (3388)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (3390)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (3405)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (3389)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (3387)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (3410)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (3390)Refutation not found, incomplete strategy% (3390)------------------------------
% 0.20/0.51  % (3390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3390)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3390)Memory used [KB]: 6140
% 0.20/0.51  % (3390)Time elapsed: 0.106 s
% 0.20/0.51  % (3390)------------------------------
% 0.20/0.51  % (3390)------------------------------
% 1.19/0.51  % (3393)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.19/0.51  % (3399)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.19/0.51  % (3408)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.19/0.51  % (3393)Refutation found. Thanks to Tanya!
% 1.19/0.51  % SZS status Theorem for theBenchmark
% 1.19/0.51  % SZS output start Proof for theBenchmark
% 1.19/0.51  fof(f77,plain,(
% 1.19/0.51    $false),
% 1.19/0.51    inference(subsumption_resolution,[],[f32,f75])).
% 1.19/0.51  fof(f75,plain,(
% 1.19/0.51    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 1.19/0.51    inference(resolution,[],[f73,f39])).
% 1.19/0.51  fof(f39,plain,(
% 1.19/0.51    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.19/0.51    inference(cnf_transformation,[],[f21])).
% 1.19/0.51  fof(f21,plain,(
% 1.19/0.51    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.19/0.51    inference(ennf_transformation,[],[f4])).
% 1.19/0.51  fof(f4,axiom,(
% 1.19/0.51    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.19/0.51  fof(f73,plain,(
% 1.19/0.51    ( ! [X0,X1] : (r1_xboole_0(k10_relat_1(k1_xboole_0,X1),X0)) )),
% 1.19/0.51    inference(subsumption_resolution,[],[f71,f57])).
% 1.19/0.51  fof(f57,plain,(
% 1.19/0.51    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.19/0.51    inference(resolution,[],[f56,f42])).
% 1.19/0.51  % (3398)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.51  fof(f42,plain,(
% 1.19/0.51    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f31])).
% 1.19/0.51  fof(f31,plain,(
% 1.19/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f30])).
% 1.19/0.51  fof(f30,plain,(
% 1.19/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.19/0.51    introduced(choice_axiom,[])).
% 1.19/0.51  fof(f23,plain,(
% 1.19/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.19/0.51    inference(ennf_transformation,[],[f19])).
% 1.19/0.51  fof(f19,plain,(
% 1.19/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.19/0.51    inference(rectify,[],[f1])).
% 1.19/0.51  fof(f1,axiom,(
% 1.19/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.19/0.51  fof(f56,plain,(
% 1.19/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.19/0.51    inference(resolution,[],[f48,f37])).
% 1.19/0.51  fof(f37,plain,(
% 1.19/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f3])).
% 1.19/0.51  fof(f3,axiom,(
% 1.19/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.19/0.51  fof(f48,plain,(
% 1.19/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f27])).
% 1.19/0.51  fof(f27,plain,(
% 1.19/0.51    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.19/0.51    inference(ennf_transformation,[],[f11])).
% 1.19/0.51  fof(f11,axiom,(
% 1.19/0.51    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.19/0.51  fof(f71,plain,(
% 1.19/0.51    ( ! [X0,X1] : (~r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(k10_relat_1(k1_xboole_0,X1),X0)) )),
% 1.19/0.51    inference(resolution,[],[f70,f47])).
% 1.19/0.51  fof(f47,plain,(
% 1.19/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f26])).
% 1.19/0.51  fof(f26,plain,(
% 1.19/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.19/0.51    inference(flattening,[],[f25])).
% 1.19/0.51  fof(f25,plain,(
% 1.19/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.19/0.51    inference(ennf_transformation,[],[f2])).
% 1.19/0.51  fof(f2,axiom,(
% 1.19/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.19/0.51  fof(f70,plain,(
% 1.19/0.51    ( ! [X2] : (r1_tarski(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)) )),
% 1.19/0.51    inference(forward_demodulation,[],[f69,f63])).
% 1.19/0.51  fof(f63,plain,(
% 1.19/0.51    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.19/0.51    inference(forward_demodulation,[],[f62,f34])).
% 1.19/0.51  fof(f34,plain,(
% 1.19/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.19/0.51    inference(cnf_transformation,[],[f15])).
% 1.19/0.51  fof(f15,axiom,(
% 1.19/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.19/0.51  fof(f62,plain,(
% 1.19/0.51    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.19/0.51    inference(forward_demodulation,[],[f61,f35])).
% 1.19/0.51  fof(f35,plain,(
% 1.19/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.19/0.51    inference(cnf_transformation,[],[f15])).
% 1.19/0.51  fof(f61,plain,(
% 1.19/0.51    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 1.19/0.51    inference(resolution,[],[f40,f54])).
% 1.19/0.51  fof(f54,plain,(
% 1.19/0.51    v1_relat_1(k1_xboole_0)),
% 1.19/0.51    inference(superposition,[],[f36,f33])).
% 1.19/0.51  fof(f33,plain,(
% 1.19/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.19/0.51    inference(cnf_transformation,[],[f16])).
% 1.19/0.51  fof(f16,axiom,(
% 1.19/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.19/0.51  fof(f36,plain,(
% 1.19/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f12])).
% 1.19/0.51  fof(f12,axiom,(
% 1.19/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.19/0.51  fof(f40,plain,(
% 1.19/0.51    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f22])).
% 1.19/0.51  fof(f22,plain,(
% 1.19/0.51    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.19/0.51    inference(ennf_transformation,[],[f13])).
% 1.19/0.51  fof(f13,axiom,(
% 1.19/0.51    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.19/0.51  fof(f69,plain,(
% 1.19/0.51    ( ! [X2] : (r1_tarski(k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,k1_xboole_0))) )),
% 1.19/0.51    inference(forward_demodulation,[],[f67,f35])).
% 1.19/0.51  fof(f67,plain,(
% 1.19/0.51    ( ! [X2] : (r1_tarski(k10_relat_1(k1_xboole_0,X2),k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)))) )),
% 1.19/0.51    inference(resolution,[],[f45,f54])).
% 1.19/0.51  fof(f45,plain,(
% 1.19/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f24])).
% 1.19/0.51  fof(f24,plain,(
% 1.19/0.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.19/0.51    inference(ennf_transformation,[],[f14])).
% 1.19/0.51  fof(f14,axiom,(
% 1.19/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).
% 1.19/0.51  fof(f32,plain,(
% 1.19/0.51    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.19/0.51    inference(cnf_transformation,[],[f29])).
% 1.19/0.51  fof(f29,plain,(
% 1.19/0.51    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f28])).
% 1.19/0.51  fof(f28,plain,(
% 1.19/0.51    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.19/0.51    introduced(choice_axiom,[])).
% 1.19/0.51  fof(f20,plain,(
% 1.19/0.51    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.19/0.51    inference(ennf_transformation,[],[f18])).
% 1.19/0.51  fof(f18,negated_conjecture,(
% 1.19/0.51    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.19/0.51    inference(negated_conjecture,[],[f17])).
% 1.19/0.51  fof(f17,conjecture,(
% 1.19/0.51    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 1.19/0.51  % SZS output end Proof for theBenchmark
% 1.19/0.51  % (3393)------------------------------
% 1.19/0.51  % (3393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (3393)Termination reason: Refutation
% 1.19/0.51  
% 1.19/0.51  % (3393)Memory used [KB]: 6268
% 1.19/0.51  % (3393)Time elapsed: 0.073 s
% 1.19/0.51  % (3393)------------------------------
% 1.19/0.51  % (3393)------------------------------
% 1.19/0.51  % (3382)Success in time 0.156 s
%------------------------------------------------------------------------------
