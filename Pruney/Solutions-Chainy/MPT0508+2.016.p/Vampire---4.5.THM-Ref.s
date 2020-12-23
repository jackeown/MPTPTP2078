%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  88 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 382 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(resolution,[],[f200,f29])).

fof(f29,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f200,plain,(
    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f198,f120])).

fof(f120,plain,(
    r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f119,f26])).

fof(f26,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f119,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f95,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f95,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1)) ),
    inference(superposition,[],[f31,f62])).

fof(f62,plain,(
    k7_relat_1(k7_relat_1(sK3,sK1),sK0) = k7_relat_1(sK3,sK0) ),
    inference(resolution,[],[f53,f28])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k7_relat_1(k7_relat_1(sK3,X3),X2) = k7_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f35,f26])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k7_relat_1(sK3,X0),X1)
      | r1_tarski(k7_relat_1(sK2,X0),X1) ) ),
    inference(superposition,[],[f36,f197])).

fof(f197,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0)) ),
    inference(resolution,[],[f196,f26])).

fof(f196,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3)
      | k7_relat_1(sK3,X0) = k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0)) ) ),
    inference(resolution,[],[f100,f27])).

fof(f27,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,X0)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k2_xboole_0(k7_relat_1(sK2,X1),k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f50,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X1,X2) = k2_xboole_0(k7_relat_1(X0,X2),k7_relat_1(X1,X2)) ) ),
    inference(resolution,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.47  % (15085)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.47  % (15094)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.48  % (15080)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.48  % (15085)Refutation not found, incomplete strategy% (15085)------------------------------
% 0.22/0.48  % (15085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (15085)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (15085)Memory used [KB]: 10490
% 0.22/0.48  % (15085)Time elapsed: 0.065 s
% 0.22/0.48  % (15085)------------------------------
% 0.22/0.48  % (15085)------------------------------
% 0.22/0.50  % (15078)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (15076)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (15078)Refutation not found, incomplete strategy% (15078)------------------------------
% 0.22/0.50  % (15078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15078)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (15078)Memory used [KB]: 10490
% 0.22/0.50  % (15078)Time elapsed: 0.090 s
% 0.22/0.50  % (15078)------------------------------
% 0.22/0.50  % (15078)------------------------------
% 0.22/0.51  % (15079)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (15092)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (15084)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (15084)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(resolution,[],[f200,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.22/0.51    inference(resolution,[],[f198,f120])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1))),
% 0.22/0.51    inference(resolution,[],[f119,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    v1_relat_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    ~v1_relat_1(sK3) | r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1))),
% 0.22/0.51    inference(resolution,[],[f95,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ~v1_relat_1(k7_relat_1(sK3,sK1)) | r1_tarski(k7_relat_1(sK3,sK0),k7_relat_1(sK3,sK1))),
% 0.22/0.51    inference(superposition,[],[f31,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    k7_relat_1(k7_relat_1(sK3,sK1),sK0) = k7_relat_1(sK3,sK0)),
% 0.22/0.51    inference(resolution,[],[f53,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    r1_tarski(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k7_relat_1(k7_relat_1(sK3,X3),X2) = k7_relat_1(sK3,X2)) )),
% 0.22/0.51    inference(resolution,[],[f35,f26])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k7_relat_1(sK3,X0),X1) | r1_tarski(k7_relat_1(sK2,X0),X1)) )),
% 0.22/0.52    inference(superposition,[],[f36,f197])).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))) )),
% 0.22/0.52    inference(resolution,[],[f196,f26])).
% 0.22/0.52  fof(f196,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_relat_1(sK3) | k7_relat_1(sK3,X0) = k2_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK3,X0))) )),
% 0.22/0.52    inference(resolution,[],[f100,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    r1_tarski(sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(sK2,X0) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k2_xboole_0(k7_relat_1(sK2,X1),k7_relat_1(X0,X1))) )),
% 0.22/0.52    inference(resolution,[],[f50,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | k7_relat_1(X1,X2) = k2_xboole_0(k7_relat_1(X0,X2),k7_relat_1(X1,X2))) )),
% 0.22/0.52    inference(resolution,[],[f32,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (15084)------------------------------
% 0.22/0.52  % (15084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15084)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (15084)Memory used [KB]: 1791
% 0.22/0.52  % (15084)Time elapsed: 0.106 s
% 0.22/0.52  % (15084)------------------------------
% 0.22/0.52  % (15084)------------------------------
% 0.22/0.52  % (15070)Success in time 0.159 s
%------------------------------------------------------------------------------
