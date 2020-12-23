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
% DateTime   : Thu Dec  3 12:43:03 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 128 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 233 expanded)
%              Number of equality atoms :   21 (  71 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2000,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1999,f241])).

fof(f241,plain,(
    ! [X2] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X2)),sK3)) ),
    inference(superposition,[],[f117,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f38,f33,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f117,plain,(
    ! [X0] : r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X0))) ),
    inference(resolution,[],[f114,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f114,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X2)
      | r1_tarski(sK0,X2) ) ),
    inference(superposition,[],[f54,f104])).

fof(f104,plain,(
    k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3))) ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f44,f33])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1999,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3)) ),
    inference(subsumption_resolution,[],[f1968,f966])).

fof(f966,plain,(
    ! [X14] : r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(X14,sK4)),sK5)) ),
    inference(resolution,[],[f245,f575])).

fof(f575,plain,(
    ! [X18] : r1_tarski(k4_xboole_0(sK1,X18),k2_zfmisc_1(sK4,sK5)) ),
    inference(superposition,[],[f377,f105])).

fof(f105,plain,(
    k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5))) ),
    inference(resolution,[],[f49,f30])).

fof(f30,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f26])).

fof(f377,plain,(
    ! [X4,X2,X3] : r1_tarski(k4_xboole_0(X2,X3),k3_tarski(k2_tarski(X2,X4))) ),
    inference(superposition,[],[f110,f102])).

fof(f102,plain,(
    ! [X6,X5] : k3_tarski(k2_tarski(k4_xboole_0(X5,X6),X5)) = X5 ),
    inference(resolution,[],[f49,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f41,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f110,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X2,X3)),X4))) ),
    inference(resolution,[],[f54,f48])).

fof(f245,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_tarski(k4_xboole_0(X15,k2_zfmisc_1(X12,X13)),k2_zfmisc_1(X14,X13))
      | r1_tarski(X15,k2_zfmisc_1(k3_tarski(k2_tarski(X12,X14)),X13)) ) ),
    inference(superposition,[],[f53,f51])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f43,f33])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1968,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3)) ),
    inference(resolution,[],[f280,f47])).

fof(f47,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f31,f33,f33,f33])).

fof(f31,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f26])).

fof(f280,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( r1_tarski(k3_tarski(k2_tarski(X10,X11)),k2_zfmisc_1(X7,k3_tarski(k2_tarski(X8,X9))))
      | ~ r1_tarski(X11,k2_zfmisc_1(X7,X9))
      | ~ r1_tarski(X10,k2_zfmisc_1(X7,X8)) ) ),
    inference(superposition,[],[f55,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f39,f33,f33])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f33,f33])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n006.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 11:29:22 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.23/0.51  % (26432)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.14/0.53  % (26442)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.14/0.53  % (26424)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.14/0.53  % (26441)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.14/0.53  % (26440)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.14/0.53  % (26433)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.14/0.53  % (26425)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.14/0.53  % (26436)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.14/0.54  % (26431)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.27/0.54  % (26448)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.54  % (26421)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.54  % (26449)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.27/0.54  % (26429)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.27/0.55  % (26422)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.55  % (26447)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.27/0.55  % (26419)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.55  % (26426)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.27/0.55  % (26446)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.27/0.56  % (26437)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.27/0.56  % (26430)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.27/0.56  % (26438)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.27/0.56  % (26439)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.27/0.56  % (26427)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.27/0.56  % (26435)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.27/0.56  % (26428)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.27/0.57  % (26418)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.57  % (26445)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.27/0.58  % (26434)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.27/0.58  % (26423)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.27/0.59  % (26443)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.93/0.67  % (26425)Refutation found. Thanks to Tanya!
% 1.93/0.67  % SZS status Theorem for theBenchmark
% 1.93/0.67  % SZS output start Proof for theBenchmark
% 1.93/0.67  fof(f2000,plain,(
% 1.93/0.67    $false),
% 1.93/0.67    inference(subsumption_resolution,[],[f1999,f241])).
% 1.93/0.67  fof(f241,plain,(
% 1.93/0.67    ( ! [X2] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X2)),sK3))) )),
% 1.93/0.67    inference(superposition,[],[f117,f51])).
% 1.93/0.67  fof(f51,plain,(
% 1.93/0.67    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 1.93/0.67    inference(definition_unfolding,[],[f38,f33,f33])).
% 1.93/0.67  fof(f33,plain,(
% 1.93/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.93/0.67    inference(cnf_transformation,[],[f10])).
% 1.93/0.67  fof(f10,axiom,(
% 1.93/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.93/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.93/0.67  fof(f38,plain,(
% 1.93/0.67    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.93/0.67    inference(cnf_transformation,[],[f11])).
% 1.93/0.67  fof(f11,axiom,(
% 1.93/0.67    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.93/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 1.93/0.67  fof(f117,plain,(
% 1.93/0.67    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X0)))) )),
% 1.93/0.67    inference(resolution,[],[f114,f48])).
% 1.93/0.67  fof(f48,plain,(
% 1.93/0.67    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 1.93/0.67    inference(definition_unfolding,[],[f32,f33])).
% 1.93/0.67  fof(f32,plain,(
% 1.93/0.67    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.93/0.67    inference(cnf_transformation,[],[f8])).
% 1.93/0.67  fof(f8,axiom,(
% 1.93/0.67    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.93/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.93/0.67  fof(f114,plain,(
% 1.93/0.67    ( ! [X2] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X2) | r1_tarski(sK0,X2)) )),
% 1.93/0.67    inference(superposition,[],[f54,f104])).
% 1.93/0.67  fof(f104,plain,(
% 1.93/0.67    k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 1.93/0.67    inference(resolution,[],[f49,f29])).
% 1.93/0.67  fof(f29,plain,(
% 1.93/0.67    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.93/0.67    inference(cnf_transformation,[],[f26])).
% 1.93/0.67  fof(f26,plain,(
% 1.93/0.67    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.93/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f25])).
% 1.93/0.67  fof(f25,plain,(
% 1.93/0.67    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 1.93/0.67    introduced(choice_axiom,[])).
% 1.93/0.67  fof(f15,plain,(
% 1.93/0.67    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 1.93/0.67    inference(flattening,[],[f14])).
% 1.93/0.67  fof(f14,plain,(
% 1.93/0.67    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 1.93/0.67    inference(ennf_transformation,[],[f13])).
% 1.93/0.67  fof(f13,negated_conjecture,(
% 1.93/0.67    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.93/0.67    inference(negated_conjecture,[],[f12])).
% 1.93/0.67  fof(f12,conjecture,(
% 1.93/0.67    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.93/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 1.93/0.67  fof(f49,plain,(
% 1.93/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1) )),
% 1.93/0.67    inference(definition_unfolding,[],[f34,f33])).
% 1.93/0.67  fof(f34,plain,(
% 1.93/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.93/0.67    inference(cnf_transformation,[],[f16])).
% 1.93/0.67  fof(f16,plain,(
% 1.93/0.67    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.93/0.67    inference(ennf_transformation,[],[f4])).
% 1.93/0.67  fof(f4,axiom,(
% 1.93/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.93/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.93/0.67  fof(f54,plain,(
% 1.93/0.67    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.93/0.67    inference(definition_unfolding,[],[f44,f33])).
% 1.93/0.67  fof(f44,plain,(
% 1.93/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.93/0.67    inference(cnf_transformation,[],[f20])).
% 1.93/0.67  fof(f20,plain,(
% 1.93/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.93/0.67    inference(ennf_transformation,[],[f3])).
% 1.93/0.67  fof(f3,axiom,(
% 1.93/0.67    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.93/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.93/0.67  fof(f1999,plain,(
% 1.93/0.67    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3))),
% 1.93/0.67    inference(subsumption_resolution,[],[f1968,f966])).
% 1.93/0.67  fof(f966,plain,(
% 1.93/0.67    ( ! [X14] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(X14,sK4)),sK5))) )),
% 1.93/0.67    inference(resolution,[],[f245,f575])).
% 1.93/0.67  fof(f575,plain,(
% 1.93/0.67    ( ! [X18] : (r1_tarski(k4_xboole_0(sK1,X18),k2_zfmisc_1(sK4,sK5))) )),
% 1.93/0.67    inference(superposition,[],[f377,f105])).
% 1.93/0.67  fof(f105,plain,(
% 1.93/0.67    k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5)))),
% 1.93/0.67    inference(resolution,[],[f49,f30])).
% 1.93/0.67  fof(f30,plain,(
% 1.93/0.67    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.93/0.67    inference(cnf_transformation,[],[f26])).
% 1.93/0.67  fof(f377,plain,(
% 1.93/0.67    ( ! [X4,X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),k3_tarski(k2_tarski(X2,X4)))) )),
% 1.93/0.67    inference(superposition,[],[f110,f102])).
% 1.93/0.67  fof(f102,plain,(
% 1.93/0.67    ( ! [X6,X5] : (k3_tarski(k2_tarski(k4_xboole_0(X5,X6),X5)) = X5) )),
% 1.93/0.67    inference(resolution,[],[f49,f58])).
% 1.93/0.67  fof(f58,plain,(
% 1.93/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.93/0.67    inference(resolution,[],[f41,f56])).
% 1.93/0.67  fof(f56,plain,(
% 1.93/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.93/0.67    inference(equality_resolution,[],[f36])).
% 1.93/0.67  fof(f36,plain,(
% 1.93/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.93/0.67    inference(cnf_transformation,[],[f28])).
% 1.93/0.67  fof(f28,plain,(
% 1.93/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.93/0.67    inference(flattening,[],[f27])).
% 1.93/0.67  fof(f27,plain,(
% 1.93/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.93/0.67    inference(nnf_transformation,[],[f1])).
% 1.93/0.67  fof(f1,axiom,(
% 1.93/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.93/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.93/0.67  fof(f41,plain,(
% 1.93/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 1.93/0.67    inference(cnf_transformation,[],[f18])).
% 1.93/0.67  fof(f18,plain,(
% 1.93/0.67    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.93/0.67    inference(ennf_transformation,[],[f2])).
% 1.93/0.67  fof(f2,axiom,(
% 1.93/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.93/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.93/0.67  fof(f110,plain,(
% 1.93/0.67    ( ! [X4,X2,X3] : (r1_tarski(X2,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X2,X3)),X4)))) )),
% 1.93/0.67    inference(resolution,[],[f54,f48])).
% 1.93/0.67  fof(f245,plain,(
% 1.93/0.67    ( ! [X14,X12,X15,X13] : (~r1_tarski(k4_xboole_0(X15,k2_zfmisc_1(X12,X13)),k2_zfmisc_1(X14,X13)) | r1_tarski(X15,k2_zfmisc_1(k3_tarski(k2_tarski(X12,X14)),X13))) )),
% 1.93/0.67    inference(superposition,[],[f53,f51])).
% 1.93/0.67  fof(f53,plain,(
% 1.93/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.93/0.67    inference(definition_unfolding,[],[f43,f33])).
% 1.93/0.67  fof(f43,plain,(
% 1.93/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.93/0.67    inference(cnf_transformation,[],[f19])).
% 1.93/0.67  fof(f19,plain,(
% 1.93/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.93/0.67    inference(ennf_transformation,[],[f7])).
% 1.93/0.67  fof(f7,axiom,(
% 1.93/0.67    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.93/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.93/0.67  fof(f1968,plain,(
% 1.93/0.67    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5)) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3))),
% 1.93/0.67    inference(resolution,[],[f280,f47])).
% 1.93/0.67  fof(f47,plain,(
% 1.93/0.67    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 1.93/0.67    inference(definition_unfolding,[],[f31,f33,f33,f33])).
% 1.93/0.67  fof(f31,plain,(
% 1.93/0.67    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.93/0.67    inference(cnf_transformation,[],[f26])).
% 1.93/0.67  fof(f280,plain,(
% 1.93/0.67    ( ! [X10,X8,X7,X11,X9] : (r1_tarski(k3_tarski(k2_tarski(X10,X11)),k2_zfmisc_1(X7,k3_tarski(k2_tarski(X8,X9)))) | ~r1_tarski(X11,k2_zfmisc_1(X7,X9)) | ~r1_tarski(X10,k2_zfmisc_1(X7,X8))) )),
% 1.93/0.67    inference(superposition,[],[f55,f50])).
% 1.93/0.67  fof(f50,plain,(
% 1.93/0.67    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 1.93/0.67    inference(definition_unfolding,[],[f39,f33,f33])).
% 1.93/0.67  fof(f39,plain,(
% 1.93/0.67    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.93/0.67    inference(cnf_transformation,[],[f11])).
% 1.93/0.67  fof(f55,plain,(
% 1.93/0.67    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.93/0.67    inference(definition_unfolding,[],[f46,f33,f33])).
% 1.93/0.67  fof(f46,plain,(
% 1.93/0.67    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.93/0.67    inference(cnf_transformation,[],[f24])).
% 1.93/0.67  fof(f24,plain,(
% 1.93/0.67    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.93/0.67    inference(flattening,[],[f23])).
% 1.93/0.67  fof(f23,plain,(
% 1.93/0.67    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.93/0.67    inference(ennf_transformation,[],[f5])).
% 1.93/0.67  fof(f5,axiom,(
% 1.93/0.67    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 1.93/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
% 1.93/0.67  % SZS output end Proof for theBenchmark
% 1.93/0.67  % (26425)------------------------------
% 1.93/0.67  % (26425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.67  % (26425)Termination reason: Refutation
% 1.93/0.67  
% 1.93/0.67  % (26425)Memory used [KB]: 12792
% 1.93/0.67  % (26425)Time elapsed: 0.207 s
% 1.93/0.67  % (26425)------------------------------
% 1.93/0.67  % (26425)------------------------------
% 1.93/0.68  % (26413)Success in time 0.301 s
%------------------------------------------------------------------------------
