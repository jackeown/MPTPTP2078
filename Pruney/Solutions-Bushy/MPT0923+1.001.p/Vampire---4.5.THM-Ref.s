%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0923+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  93 expanded)
%              Number of leaves         :    5 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 284 expanded)
%              Number of equality atoms :   24 (  71 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f90,f34])).

fof(f34,plain,(
    sK0 = k4_tarski(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK10(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK9(X0,X1,X3),sK10(X0,X1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK9(X0,X1,X3),sK10(X0,X1,X3)) = X3
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

fof(f25,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f10,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f10,plain,(
    r2_hidden(sK0,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( k4_mcart_1(X5,X6,X7,X8) != X0
          | ~ r2_hidden(X8,X4)
          | ~ r2_hidden(X7,X3)
          | ~ r2_hidden(X6,X2)
          | ~ r2_hidden(X5,X1) )
      & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( ! [X5,X6,X7,X8] :
              ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
                & r2_hidden(X8,X4)
                & r2_hidden(X7,X3)
                & r2_hidden(X6,X2)
                & r2_hidden(X5,X1) )
          & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( ! [X5,X6,X7,X8] :
            ~ ( k4_mcart_1(X5,X6,X7,X8) = X0
              & r2_hidden(X8,X4)
              & r2_hidden(X7,X3)
              & r2_hidden(X6,X2)
              & r2_hidden(X5,X1) )
        & r2_hidden(X0,k4_zfmisc_1(X1,X2,X3,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

fof(f90,plain,(
    sK0 != k4_tarski(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK10(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)) ),
    inference(forward_demodulation,[],[f77,f47])).

fof(f47,plain,(
    sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0) = k3_mcart_1(sK5(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK1,sK2,sK3),sK6(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK1,sK2,sK3),sK7(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f32,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

% (31532)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (31536)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (31556)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (31534)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (31540)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (31537)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (31554)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (31553)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (31551)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (31546)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (31548)Refutation not found, incomplete strategy% (31548)------------------------------
% (31548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31548)Termination reason: Refutation not found, incomplete strategy

% (31548)Memory used [KB]: 10618
% (31548)Time elapsed: 0.120 s
% (31548)------------------------------
% (31548)------------------------------
% (31544)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (31543)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f32,plain,(
    r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK9(X0,X1,X3),X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f77,plain,(
    sK0 != k4_tarski(k3_mcart_1(sK5(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK1,sK2,sK3),sK6(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK1,sK2,sK3),sK7(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK1,sK2,sK3)),sK10(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f33,f45,f46,f26])).

fof(f26,plain,(
    ! [X6,X8,X7,X5] :
      ( sK0 != k4_tarski(k3_mcart_1(X5,X6,X7),X8)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X8,sK4)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(definition_unfolding,[],[f9,f11])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f9,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3)
      | ~ r2_hidden(X8,sK4)
      | k4_mcart_1(X5,X6,X7,X8) != sK0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    r2_hidden(sK7(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK1,sK2,sK3),sK3) ),
    inference(unit_resulting_resolution,[],[f32,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,(
    r2_hidden(sK6(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK1,sK2,sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f32,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | r2_hidden(sK6(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    r2_hidden(sK10(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK4) ),
    inference(unit_resulting_resolution,[],[f25,f30])).

% (31552)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK10(X0,X1,X3),X1) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK10(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f44,plain,(
    r2_hidden(sK5(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK1,sK2,sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f32,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | r2_hidden(sK5(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
