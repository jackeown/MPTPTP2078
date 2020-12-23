%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 277 expanded)
%              Number of leaves         :    7 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          :  134 ( 603 expanded)
%              Number of equality atoms :   14 ( 154 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139,f106])).

fof(f106,plain,(
    r2_hidden(sK0,sK4) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(sK0,sK4) ),
    inference(resolution,[],[f86,f35])).

fof(f35,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | r2_hidden(sK0,sK4) ),
    inference(definition_unfolding,[],[f11,f26,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f25,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f11,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <~> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      <=> ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <=> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).

fof(f86,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | r2_hidden(sK0,sK4) ) ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | r2_hidden(X0,X3) ) ),
    inference(definition_unfolding,[],[f27,f15,f16])).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X0,X3)
      | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).

fof(f80,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
      | r2_hidden(sK0,sK4) ) ),
    inference(resolution,[],[f68,f35])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X4),k2_zfmisc_1(X1,X5))
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f40,f42])).

fof(f42,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f139,plain,(
    ~ r2_hidden(sK0,sK4) ),
    inference(subsumption_resolution,[],[f138,f69])).

fof(f69,plain,(
    r2_hidden(sK1,sK5) ),
    inference(subsumption_resolution,[],[f65,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X0),k2_zfmisc_1(X5,X1))
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f39,f42])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | r2_hidden(X1,X4) ) ),
    inference(definition_unfolding,[],[f28,f15,f16])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X1,X4)
      | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(sK1,sK5) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | r2_hidden(sK1,sK5) ),
    inference(definition_unfolding,[],[f12,f26,f31])).

fof(f12,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f138,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4) ),
    inference(resolution,[],[f135,f42])).

fof(f135,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f134,f51])).

fof(f51,plain,(
    r2_hidden(sK3,sK7) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(sK3,sK7) ),
    inference(resolution,[],[f38,f32])).

fof(f32,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | r2_hidden(sK3,sK7) ),
    inference(definition_unfolding,[],[f14,f26,f31])).

fof(f14,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | r2_hidden(X2,X5) ) ),
    inference(definition_unfolding,[],[f29,f15,f16])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X2,X5)
      | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f134,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    inference(subsumption_resolution,[],[f132,f57])).

fof(f57,plain,(
    r2_hidden(sK2,sK6) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(sK2,sK6) ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | r2_hidden(sK2,sK6) ),
    inference(definition_unfolding,[],[f13,f26,f31])).

fof(f13,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f132,plain,
    ( ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f127,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X2,X5)
      | ~ r2_hidden(X0,X3) ) ),
    inference(definition_unfolding,[],[f30,f15,f16])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X0,X3)
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X2,X5)
      | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f127,plain,(
    ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(subsumption_resolution,[],[f126,f51])).

fof(f126,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(subsumption_resolution,[],[f125,f57])).

fof(f125,plain,
    ( ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(subsumption_resolution,[],[f124,f106])).

fof(f124,plain,
    ( ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(resolution,[],[f36,f69])).

fof(f36,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f10,f26,f31])).

fof(f10,plain,
    ( ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (30265)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (30279)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (30257)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (30271)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (30261)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (30269)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (30273)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (30277)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (30273)Refutation not found, incomplete strategy% (30273)------------------------------
% 0.22/0.53  % (30273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30273)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (30273)Memory used [KB]: 10618
% 0.22/0.53  % (30273)Time elapsed: 0.127 s
% 0.22/0.53  % (30273)------------------------------
% 0.22/0.53  % (30273)------------------------------
% 0.22/0.53  % (30259)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (30262)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (30268)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (30262)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f140,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f139,f106])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    r2_hidden(sK0,sK4)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    r2_hidden(sK0,sK4) | r2_hidden(sK0,sK4)),
% 0.22/0.54    inference(resolution,[],[f86,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | r2_hidden(sK0,sK4)),
% 0.22/0.54    inference(definition_unfolding,[],[f11,f26,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f25,f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    r2_hidden(sK0,sK4) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <~> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.22/0.54    inference(negated_conjecture,[],[f7])).
% 0.22/0.54  fof(f7,conjecture,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_mcart_1)).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X6,X7] : (~r2_hidden(X6,X7) | r2_hidden(sK0,sK4)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f80,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | r2_hidden(X0,X3)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f27,f15,f16])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X0,X3) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <=> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ( ! [X6,X7] : (~r2_hidden(X6,X7) | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | r2_hidden(sK0,sK4)) )),
% 0.22/0.54    inference(resolution,[],[f68,f35])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(k4_tarski(X0,X4),k2_zfmisc_1(X1,X5)) | ~r2_hidden(X2,X3) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f40,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.54    inference(equality_resolution,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK4)),
% 0.22/0.54    inference(subsumption_resolution,[],[f138,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    r2_hidden(sK1,sK5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f65,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(k4_tarski(X4,X0),k2_zfmisc_1(X5,X1)) | ~r2_hidden(X2,X3) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(resolution,[],[f39,f42])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | r2_hidden(X1,X4)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f15,f16])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X1,X4) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | r2_hidden(sK1,sK5)),
% 0.22/0.54    inference(resolution,[],[f40,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | r2_hidden(sK1,sK5)),
% 0.22/0.54    inference(definition_unfolding,[],[f12,f26,f31])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    r2_hidden(sK1,sK5) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4)),
% 0.22/0.54    inference(resolution,[],[f135,f42])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))),
% 0.22/0.54    inference(subsumption_resolution,[],[f134,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    r2_hidden(sK3,sK7)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    r2_hidden(sK3,sK7) | r2_hidden(sK3,sK7)),
% 0.22/0.54    inference(resolution,[],[f38,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | r2_hidden(sK3,sK7)),
% 0.22/0.54    inference(definition_unfolding,[],[f14,f26,f31])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    r2_hidden(sK3,sK7) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | r2_hidden(X2,X5)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f15,f16])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X2,X5) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))),
% 0.22/0.54    inference(subsumption_resolution,[],[f132,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    r2_hidden(sK2,sK6)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    r2_hidden(sK2,sK6) | r2_hidden(sK2,sK6)),
% 0.22/0.54    inference(resolution,[],[f39,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | r2_hidden(sK2,sK6)),
% 0.22/0.54    inference(definition_unfolding,[],[f13,f26,f31])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    r2_hidden(sK2,sK6) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ~r2_hidden(sK2,sK6) | ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))),
% 0.22/0.54    inference(resolution,[],[f127,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | ~r2_hidden(X1,X4) | ~r2_hidden(X2,X5) | ~r2_hidden(X0,X3)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f30,f15,f16])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X0,X3) | ~r2_hidden(X1,X4) | ~r2_hidden(X2,X5) | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f127,plain,(
% 0.22/0.54    ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.22/0.54    inference(subsumption_resolution,[],[f126,f51])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.22/0.54    inference(subsumption_resolution,[],[f125,f57])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ~r2_hidden(sK2,sK6) | ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.22/0.54    inference(subsumption_resolution,[],[f124,f106])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK4) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.22/0.54    inference(resolution,[],[f36,f69])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.22/0.54    inference(definition_unfolding,[],[f10,f26,f31])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK4) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (30262)------------------------------
% 0.22/0.54  % (30262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30262)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (30262)Memory used [KB]: 6268
% 0.22/0.54  % (30262)Time elapsed: 0.128 s
% 0.22/0.54  % (30262)------------------------------
% 0.22/0.54  % (30262)------------------------------
% 0.22/0.54  % (30260)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (30272)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (30255)Success in time 0.175 s
%------------------------------------------------------------------------------
