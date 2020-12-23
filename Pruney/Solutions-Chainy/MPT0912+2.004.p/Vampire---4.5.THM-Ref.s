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
% DateTime   : Thu Dec  3 12:59:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  99 expanded)
%              Number of leaves         :    7 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 309 expanded)
%              Number of equality atoms :   24 (  66 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(subsumption_resolution,[],[f40,f27])).

fof(f27,plain,(
    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(subsumption_resolution,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f26,plain,
    ( sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))
    | ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(resolution,[],[f23,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f23,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f14,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f14,plain,(
    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X4,X5,X6] :
        ( k3_mcart_1(X4,X5,X6) != sK0
        | ~ r2_hidden(X6,sK3)
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5,X6] :
            ( k3_mcart_1(X4,X5,X6) != X0
            | ~ r2_hidden(X6,X3)
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) )
   => ( ! [X6,X5,X4] :
          ( k3_mcart_1(X4,X5,X6) != sK0
          | ~ r2_hidden(X6,sK3)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1) )
      & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) != X0
          | ~ r2_hidden(X6,X3)
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5,X6] :
              ~ ( k3_mcart_1(X4,X5,X6) = X0
                & r2_hidden(X6,X3)
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f40,plain,(
    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) ),
    inference(resolution,[],[f39,f25])).

fof(f25,plain,(
    r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(resolution,[],[f23,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | sK0 != k4_tarski(k1_mcart_1(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f38,f30])).

fof(f30,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f23,f19])).

fof(f38,plain,(
    ! [X0] :
      ( sK0 != k4_tarski(k1_mcart_1(sK0),X0)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1) ) ),
    inference(subsumption_resolution,[],[f37,f31])).

fof(f31,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2) ),
    inference(resolution,[],[f24,f20])).

fof(f37,plain,(
    ! [X0] :
      ( sK0 != k4_tarski(k1_mcart_1(sK0),X0)
      | ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1) ) ),
    inference(superposition,[],[f22,f33])).

fof(f33,plain,(
    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))) ),
    inference(subsumption_resolution,[],[f32,f21])).

fof(f32,plain,
    ( k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f24,f18])).

fof(f22,plain,(
    ! [X6,X4,X5] :
      ( sK0 != k4_tarski(k4_tarski(X4,X5),X6)
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f15,plain,(
    ! [X6,X4,X5] :
      ( k3_mcart_1(X4,X5,X6) != sK0
      | ~ r2_hidden(X6,sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:03:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (6412)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.48  % (6404)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (6397)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (6414)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (6393)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (6395)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (6393)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f40,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f26,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    sK0 = k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0)) | ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.20/0.52    inference(resolution,[],[f23,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.20/0.52    inference(definition_unfolding,[],[f14,f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))) => (! [X6,X5,X4] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK0,k3_zfmisc_1(sK1,sK2,sK3)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.20/0.52    inference(negated_conjecture,[],[f6])).
% 0.20/0.52  fof(f6,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    sK0 != k4_tarski(k1_mcart_1(sK0),k2_mcart_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f39,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(sK0),sK3)),
% 0.20/0.52    inference(resolution,[],[f23,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK3) | sK0 != k4_tarski(k1_mcart_1(sK0),X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f38,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1)),
% 0.20/0.52    inference(resolution,[],[f24,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(sK0),k2_zfmisc_1(sK1,sK2))),
% 0.20/0.52    inference(resolution,[],[f23,f19])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0] : (sK0 != k4_tarski(k1_mcart_1(sK0),X0) | ~r2_hidden(X0,sK3) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f37,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2)),
% 0.20/0.52    inference(resolution,[],[f24,f20])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (sK0 != k4_tarski(k1_mcart_1(sK0),X0) | ~r2_hidden(X0,sK3) | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK0)),sK2) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK0)),sK1)) )),
% 0.20/0.52    inference(superposition,[],[f22,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f32,f21])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    k1_mcart_1(sK0) = k4_tarski(k1_mcart_1(k1_mcart_1(sK0)),k2_mcart_1(k1_mcart_1(sK0))) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 0.20/0.52    inference(resolution,[],[f24,f18])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (sK0 != k4_tarski(k4_tarski(X4,X5),X6) | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f15,f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (k3_mcart_1(X4,X5,X6) != sK0 | ~r2_hidden(X6,sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (6393)------------------------------
% 0.20/0.52  % (6393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (6393)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (6393)Memory used [KB]: 1663
% 0.20/0.52  % (6393)Time elapsed: 0.106 s
% 0.20/0.52  % (6393)------------------------------
% 0.20/0.52  % (6393)------------------------------
% 0.20/0.52  % (6398)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (6406)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.52  % (6394)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.52  % (6392)Success in time 0.167 s
%------------------------------------------------------------------------------
