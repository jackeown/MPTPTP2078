%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  62 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   69 ( 141 expanded)
%              Number of equality atoms :    6 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(global_subsumption,[],[f14,f174])).

fof(f174,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f60,f97])).

fof(f97,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5))) ),
    inference(global_subsumption,[],[f15,f86])).

fof(f86,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5))) ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5)))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5))) ),
    inference(resolution,[],[f32,f37])).

fof(f37,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5))) ),
    inference(resolution,[],[f33,f26])).

fof(f26,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(resolution,[],[f21,f16])).

fof(f16,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f33,plain,(
    ! [X10,X8,X11,X9] :
      ( r1_tarski(X11,k2_zfmisc_1(k2_xboole_0(X8,X10),X9))
      | ~ r1_tarski(X11,k2_zfmisc_1(X10,X9)) ) ),
    inference(superposition,[],[f20,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f32,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_tarski(X7,k2_zfmisc_1(k2_xboole_0(X4,X6),X5))
      | ~ r1_tarski(X7,k2_zfmisc_1(X4,X5)) ) ),
    inference(superposition,[],[f22,f18])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f20,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f58,plain,(
    ! [X10,X8,X11,X9] :
      ( r1_tarski(X11,k2_zfmisc_1(X8,k2_xboole_0(X9,X10)))
      | ~ r1_tarski(X11,k2_zfmisc_1(X8,X10)) ) ),
    inference(superposition,[],[f20,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X19,X17,X18,X16] :
      ( r1_tarski(X19,k2_zfmisc_1(X16,k2_xboole_0(X17,X18)))
      | ~ r1_tarski(X19,k2_zfmisc_1(X16,X17)) ) ),
    inference(superposition,[],[f22,f19])).

fof(f14,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:15:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.41  % (26522)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.14/0.42  % (26519)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.14/0.42  % (26516)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.14/0.42  % (26521)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (26519)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f184,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(global_subsumption,[],[f14,f174])).
% 0.22/0.42  fof(f174,plain,(
% 0.22/0.42    ~r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.22/0.42    inference(resolution,[],[f60,f97])).
% 0.22/0.42  fof(f97,plain,(
% 0.22/0.42    ~r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5)))),
% 0.22/0.42    inference(global_subsumption,[],[f15,f86])).
% 0.22/0.42  fof(f86,plain,(
% 0.22/0.42    ~r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | ~r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5)))),
% 0.22/0.42    inference(resolution,[],[f58,f45])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5))) | ~r1_tarski(sK0,k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK5)))),
% 0.22/0.42    inference(resolution,[],[f32,f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    ~r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | ~r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5)))),
% 0.22/0.42    inference(resolution,[],[f33,f26])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ~r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) | ~r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.22/0.42    inference(resolution,[],[f21,f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f8,f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 0.22/0.42    inference(flattening,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.22/0.42    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(flattening,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ( ! [X10,X8,X11,X9] : (r1_tarski(X11,k2_zfmisc_1(k2_xboole_0(X8,X10),X9)) | ~r1_tarski(X11,k2_zfmisc_1(X10,X9))) )),
% 0.22/0.43    inference(superposition,[],[f20,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X6,X4,X7,X5] : (r1_tarski(X7,k2_zfmisc_1(k2_xboole_0(X4,X6),X5)) | ~r1_tarski(X7,k2_zfmisc_1(X4,X5))) )),
% 0.22/0.43    inference(superposition,[],[f22,f18])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1)) )),
% 0.22/0.43    inference(superposition,[],[f20,f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ( ! [X10,X8,X11,X9] : (r1_tarski(X11,k2_zfmisc_1(X8,k2_xboole_0(X9,X10))) | ~r1_tarski(X11,k2_zfmisc_1(X8,X10))) )),
% 0.22/0.43    inference(superposition,[],[f20,f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ( ! [X19,X17,X18,X16] : (r1_tarski(X19,k2_zfmisc_1(X16,k2_xboole_0(X17,X18))) | ~r1_tarski(X19,k2_zfmisc_1(X16,X17))) )),
% 0.22/0.43    inference(superposition,[],[f22,f19])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (26519)------------------------------
% 0.22/0.43  % (26519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (26519)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (26519)Memory used [KB]: 6396
% 0.22/0.43  % (26519)Time elapsed: 0.011 s
% 0.22/0.43  % (26519)------------------------------
% 0.22/0.43  % (26519)------------------------------
% 0.22/0.43  % (26514)Success in time 0.068 s
%------------------------------------------------------------------------------
