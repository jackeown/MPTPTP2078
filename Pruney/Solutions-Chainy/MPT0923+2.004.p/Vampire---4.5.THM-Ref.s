%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  77 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :   17
%              Number of atoms          :  128 ( 236 expanded)
%              Number of equality atoms :   33 (  62 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(subsumption_resolution,[],[f61,f29])).

fof(f29,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(definition_unfolding,[],[f12,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f12,plain,(
    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

fof(f61,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f60,plain,(
    ~ r2_hidden(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f59,plain,
    ( ~ r2_hidden(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4)) ),
    inference(resolution,[],[f58,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,
    ( ~ r2_hidden(sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4)
    | ~ r2_hidden(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4)
    | ~ r2_hidden(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(superposition,[],[f55,f40])).

fof(f40,plain,(
    sK0 = k4_tarski(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0)) ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK0 != k4_tarski(X1,X0)
      | ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK4)
      | sK0 != k4_tarski(X1,X0)
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
      | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ) ),
    inference(resolution,[],[f53,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X2,X3),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f25,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | r2_hidden(sK10(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK10(X0,X2,sK2,sK3),sK1)
      | ~ r2_hidden(X1,sK4)
      | k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X2,sK2),sK3)) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X0,X1) != sK0
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(sK10(X0,X2,sK2,sK3),sK1)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X2,sK2),sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X2,sK2),sK3)) ) ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK11(X0,X1,X2,X3),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f26,f14])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | r2_hidden(sK11(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK11(X0,X1,X2,sK3),sK2)
      | sK0 != k4_tarski(X0,X3)
      | ~ r2_hidden(X3,sK4)
      | ~ r2_hidden(sK10(X0,X1,X2,sK3),sK1)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),sK3)) ) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK11(X0,X1,X2,sK3),sK2)
      | sK0 != k4_tarski(X0,X3)
      | ~ r2_hidden(X3,sK4)
      | ~ r2_hidden(sK10(X0,X1,X2,sK3),sK1)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),sK3)) ) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK12(X0,X1,X2,X3),X3)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f27,f14])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | r2_hidden(sK12(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK12(X0,X1,X2,X3),sK3)
      | ~ r2_hidden(sK11(X0,X1,X2,X3),sK2)
      | sK0 != k4_tarski(X0,X4)
      | ~ r2_hidden(X4,sK4)
      | ~ r2_hidden(sK10(X0,X1,X2,X3),sK1)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ) ),
    inference(superposition,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)),sK12(X0,X1,X2,X3)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ) ),
    inference(definition_unfolding,[],[f28,f14,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | k3_mcart_1(sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3),sK12(X0,X1,X2,X3)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X6,X8,X7,X5] :
      ( sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(definition_unfolding,[],[f11,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f11,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X8,sK4)
      | k4_mcart_1(X5,X6,X7,X8) != sK0 ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (5392)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (5384)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (5376)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (5392)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (5380)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f61,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.22/0.52    inference(definition_unfolding,[],[f12,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : (k4_mcart_1(X5,X6,X7,X8) != X0 | ~r2_hidden(X8,X4) | ~r2_hidden(X7,X3) | ~r2_hidden(X6,X2) | ~r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ~(! [X5,X6,X7,X8] : ~(k4_mcart_1(X5,X6,X7,X8) = X0 & r2_hidden(X8,X4) & r2_hidden(X7,X3) & r2_hidden(X6,X2) & r2_hidden(X5,X1)) & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.22/0.52    inference(resolution,[],[f60,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~r2_hidden(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.22/0.52    inference(subsumption_resolution,[],[f59,f29])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~r2_hidden(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(sK0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4))),
% 0.22/0.52    inference(resolution,[],[f58,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ~r2_hidden(sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4) | ~r2_hidden(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    sK0 != sK0 | ~r2_hidden(sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK4) | ~r2_hidden(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 0.22/0.52    inference(superposition,[],[f55,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    sK0 = k4_tarski(sK6(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0),sK7(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3),sK4,sK0))),
% 0.22/0.52    inference(resolution,[],[f29,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_zfmisc_1(X0,X1)) | k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3) )),
% 0.22/0.52    inference(equality_resolution,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(sK6(X0,X1,X3),sK7(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (sK0 != k4_tarski(X1,X0) | ~r2_hidden(X0,sK4) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK4) | sK0 != k4_tarski(X1,X0) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))) )),
% 0.22/0.52    inference(resolution,[],[f53,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK10(X0,X1,X2,X3),X1) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f25,f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) | r2_hidden(sK10(X0,X1,X2,X3),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (? [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK10(X0,X2,sK2,sK3),sK1) | ~r2_hidden(X1,sK4) | k4_tarski(X0,X1) != sK0 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X2,sK2),sK3))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k4_tarski(X0,X1) != sK0 | ~r2_hidden(X1,sK4) | ~r2_hidden(sK10(X0,X2,sK2,sK3),sK1) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X2,sK2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X2,sK2),sK3))) )),
% 0.22/0.52    inference(resolution,[],[f51,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK11(X0,X1,X2,X3),X2) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f26,f14])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) | r2_hidden(sK11(X0,X1,X2,X3),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK11(X0,X1,X2,sK3),sK2) | sK0 != k4_tarski(X0,X3) | ~r2_hidden(X3,sK4) | ~r2_hidden(sK10(X0,X1,X2,sK3),sK1) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),sK3))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK11(X0,X1,X2,sK3),sK2) | sK0 != k4_tarski(X0,X3) | ~r2_hidden(X3,sK4) | ~r2_hidden(sK10(X0,X1,X2,sK3),sK1) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),sK3)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),sK3))) )),
% 0.22/0.52    inference(resolution,[],[f42,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(sK12(X0,X1,X2,X3),X3) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f27,f14])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) | r2_hidden(sK12(X0,X1,X2,X3),X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(sK12(X0,X1,X2,X3),sK3) | ~r2_hidden(sK11(X0,X1,X2,X3),sK2) | sK0 != k4_tarski(X0,X4) | ~r2_hidden(X4,sK4) | ~r2_hidden(sK10(X0,X1,X2,X3),sK1) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))) )),
% 0.22/0.52    inference(superposition,[],[f30,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3)),sK12(X0,X1,X2,X3)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f28,f14,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) | k3_mcart_1(sK10(X0,X1,X2,X3),sK11(X0,X1,X2,X3),sK12(X0,X1,X2,X3)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X6,X8,X7,X5] : (sK0 != k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | ~r2_hidden(X8,sK4) | ~r2_hidden(X5,sK1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f11,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ( ! [X6,X8,X7,X5] : (~r2_hidden(X5,sK1) | ~r2_hidden(X6,sK2) | ~r2_hidden(X7,sK3) | ~r2_hidden(X8,sK4) | k4_mcart_1(X5,X6,X7,X8) != sK0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (5392)------------------------------
% 0.22/0.52  % (5392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5392)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (5392)Memory used [KB]: 1791
% 0.22/0.52  % (5392)Time elapsed: 0.054 s
% 0.22/0.52  % (5392)------------------------------
% 0.22/0.52  % (5392)------------------------------
% 0.22/0.52  % (5377)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (5378)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (5370)Success in time 0.166 s
%------------------------------------------------------------------------------
