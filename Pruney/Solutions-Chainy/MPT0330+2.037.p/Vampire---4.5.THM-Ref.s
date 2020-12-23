%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 250 expanded)
%              Number of leaves         :   11 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 ( 338 expanded)
%              Number of equality atoms :   17 ( 192 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(resolution,[],[f315,f168])).

fof(f168,plain,(
    ! [X10,X11] : r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k5_enumset1(X10,X10,X10,X10,X10,X10,sK4)),k3_tarski(k5_enumset1(X11,X11,X11,X11,X11,X11,sK5)))) ),
    inference(resolution,[],[f109,f141])).

fof(f141,plain,(
    ! [X5] : r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,sK5)))) ),
    inference(resolution,[],[f81,f22])).

fof(f22,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f81,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(X8,k2_zfmisc_1(X5,X7))
      | r1_tarski(X8,k2_zfmisc_1(X5,k3_tarski(k5_enumset1(X6,X6,X6,X6,X6,X6,X7)))) ) ),
    inference(superposition,[],[f41,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_tarski(k5_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f29,f36,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f109,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ r1_tarski(X10,k2_zfmisc_1(X9,X8))
      | r1_tarski(X10,k2_zfmisc_1(k3_tarski(k5_enumset1(X7,X7,X7,X7,X7,X7,X9)),X8)) ) ),
    inference(superposition,[],[f41,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k5_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f28,f36,f36])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f315,plain,(
    ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) ),
    inference(resolution,[],[f120,f61])).

fof(f61,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK5))))
    | ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) ),
    inference(resolution,[],[f37,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f37,plain,(
    ~ r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f23,f36,f36,f36])).

fof(f23,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f20])).

fof(f120,plain,(
    ! [X0,X1] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X1)))) ),
    inference(resolution,[],[f117,f80])).

fof(f80,plain,(
    ! [X4,X2,X3] : r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4)))) ),
    inference(superposition,[],[f38,f39])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f24,f36])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f117,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X3)),sK3),X4)
      | r1_tarski(sK0,X4) ) ),
    inference(resolution,[],[f106,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f106,plain,(
    ! [X2] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X2)),sK3)) ),
    inference(superposition,[],[f46,f40])).

fof(f46,plain,(
    ! [X3] : r1_tarski(sK0,k3_tarski(k5_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X3))) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f31,f21])).

fof(f21,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (24299)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (24301)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (24300)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (24307)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (24302)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (24303)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (24311)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (24313)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (24308)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (24305)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (24314)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (24312)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (24316)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (24304)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (24315)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (24306)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (24309)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (24300)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f324,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(resolution,[],[f315,f168])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    ( ! [X10,X11] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k5_enumset1(X10,X10,X10,X10,X10,X10,sK4)),k3_tarski(k5_enumset1(X11,X11,X11,X11,X11,X11,sK5))))) )),
% 0.20/0.50    inference(resolution,[],[f109,f141])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ( ! [X5] : (r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,sK5))))) )),
% 0.20/0.50    inference(resolution,[],[f81,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.20/0.50    inference(negated_conjecture,[],[f10])).
% 0.20/0.50  fof(f10,conjecture,(
% 0.20/0.50    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X6,X8,X7,X5] : (~r1_tarski(X8,k2_zfmisc_1(X5,X7)) | r1_tarski(X8,k2_zfmisc_1(X5,k3_tarski(k5_enumset1(X6,X6,X6,X6,X6,X6,X7))))) )),
% 0.20/0.50    inference(superposition,[],[f41,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_tarski(k5_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f29,f36,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f25,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f26,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f27,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f30,f36])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ( ! [X10,X8,X7,X9] : (~r1_tarski(X10,k2_zfmisc_1(X9,X8)) | r1_tarski(X10,k2_zfmisc_1(k3_tarski(k5_enumset1(X7,X7,X7,X7,X7,X7,X9)),X8))) )),
% 0.20/0.50    inference(superposition,[],[f41,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k5_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f28,f36,f36])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK5))))),
% 0.20/0.50    inference(resolution,[],[f120,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) | ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK5))))),
% 0.20/0.50    inference(resolution,[],[f37,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f32,f36])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ~r1_tarski(k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK5))))),
% 0.20/0.50    inference(definition_unfolding,[],[f23,f36,f36,f36])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0)),k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,X1))))) )),
% 0.20/0.50    inference(resolution,[],[f117,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X4,X2,X3] : (r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4))))) )),
% 0.20/0.50    inference(superposition,[],[f38,f39])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f24,f36])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    ( ! [X4,X3] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X3)),sK3),X4) | r1_tarski(sK0,X4)) )),
% 0.20/0.50    inference(resolution,[],[f106,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X2] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X2)),sK3))) )),
% 0.20/0.50    inference(superposition,[],[f46,f40])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X3] : (r1_tarski(sK0,k3_tarski(k5_enumset1(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3),X3)))) )),
% 0.20/0.50    inference(resolution,[],[f38,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) )),
% 0.20/0.50    inference(resolution,[],[f31,f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (24300)------------------------------
% 0.20/0.50  % (24300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24300)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (24300)Memory used [KB]: 2558
% 0.20/0.50  % (24300)Time elapsed: 0.098 s
% 0.20/0.50  % (24300)------------------------------
% 0.20/0.50  % (24300)------------------------------
% 0.20/0.51  % (24298)Success in time 0.15 s
%------------------------------------------------------------------------------
