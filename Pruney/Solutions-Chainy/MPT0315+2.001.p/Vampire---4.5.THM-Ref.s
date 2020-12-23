%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:09 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 127 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 200 expanded)
%              Number of equality atoms :   41 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1805,plain,(
    $false ),
    inference(global_subsumption,[],[f14,f1802,f1804])).

fof(f1804,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f1803])).

fof(f1803,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1786,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f16,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f16,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1786,plain,
    ( k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k1_xboole_0)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f1686,f248])).

fof(f248,plain,(
    ! [X6,X4,X5,X3] :
      ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f247,f34])).

fof(f34,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f247,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X5,k4_xboole_0(X5,X6)))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f226,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f30,f38])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f226,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(k4_xboole_0(X3,X3),k4_xboole_0(X5,k4_xboole_0(X5,X6)))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f32,f21])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f29,f19,f19,f19])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f1686,plain,(
    ! [X81] : k2_zfmisc_1(sK0,sK2) != k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) ),
    inference(superposition,[],[f71,f204])).

fof(f204,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,X7))) = k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X6,k2_xboole_0(X7,X8)))) ),
    inference(forward_demodulation,[],[f188,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f188,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(k4_xboole_0(X6,X7),X8))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,X7))) ),
    inference(superposition,[],[f31,f25])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f19,f19])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f71,plain,(
    ! [X0] : k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_xboole_0(k2_zfmisc_1(sK1,sK3),X0)) ),
    inference(unit_resulting_resolution,[],[f69,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0] : ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_xboole_0(k2_zfmisc_1(sK1,sK3),X0)) ),
    inference(unit_resulting_resolution,[],[f15,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f15,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      & ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          | r1_xboole_0(X0,X1) )
       => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f1802,plain,(
    ~ r1_xboole_0(sK2,sK3) ),
    inference(trivial_inequality_removal,[],[f1801])).

fof(f1801,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f1785,f38])).

fof(f1785,plain,
    ( k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k1_xboole_0)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f1686,f257])).

fof(f257,plain,(
    ! [X6,X4,X5,X3] :
      ( k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4)))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f256,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f256,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4))) = k2_zfmisc_1(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f236,f49])).

fof(f236,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4))) = k2_zfmisc_1(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X3,X3))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f32,f21])).

fof(f14,plain,
    ( r1_xboole_0(sK2,sK3)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:56:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (658)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (635)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (638)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (635)Refutation not found, incomplete strategy% (635)------------------------------
% 0.22/0.51  % (635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (635)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (635)Memory used [KB]: 1663
% 0.22/0.51  % (635)Time elapsed: 0.105 s
% 0.22/0.51  % (635)------------------------------
% 0.22/0.51  % (635)------------------------------
% 0.22/0.51  % (657)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (666)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (674)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (655)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (673)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (640)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (637)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (639)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (664)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (636)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (663)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (661)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (659)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (663)Refutation not found, incomplete strategy% (663)------------------------------
% 0.22/0.54  % (663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (663)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (663)Memory used [KB]: 10618
% 0.22/0.54  % (663)Time elapsed: 0.126 s
% 0.22/0.54  % (663)------------------------------
% 0.22/0.54  % (663)------------------------------
% 0.22/0.54  % (641)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (642)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (668)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (672)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (656)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (670)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (668)Refutation not found, incomplete strategy% (668)------------------------------
% 0.22/0.54  % (668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (668)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (668)Memory used [KB]: 10618
% 0.22/0.54  % (668)Time elapsed: 0.100 s
% 0.22/0.54  % (668)------------------------------
% 0.22/0.54  % (668)------------------------------
% 0.22/0.55  % (656)Refutation not found, incomplete strategy% (656)------------------------------
% 0.22/0.55  % (656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (656)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (656)Memory used [KB]: 10618
% 0.22/0.55  % (656)Time elapsed: 0.139 s
% 0.22/0.55  % (656)------------------------------
% 0.22/0.55  % (656)------------------------------
% 0.22/0.55  % (671)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (660)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (669)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (662)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (665)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.55  % (655)Refutation not found, incomplete strategy% (655)------------------------------
% 1.47/0.55  % (655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (655)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (655)Memory used [KB]: 10618
% 1.47/0.55  % (655)Time elapsed: 0.149 s
% 1.47/0.55  % (655)------------------------------
% 1.47/0.55  % (655)------------------------------
% 1.47/0.55  % (643)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.55  % (667)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.57  % (675)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.19/0.67  % (678)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.19/0.67  % (677)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.19/0.67  % (676)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.19/0.68  % (679)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.19/0.70  % (680)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.19/0.72  % (670)Refutation found. Thanks to Tanya!
% 2.19/0.72  % SZS status Theorem for theBenchmark
% 2.71/0.73  % SZS output start Proof for theBenchmark
% 2.71/0.73  fof(f1805,plain,(
% 2.71/0.73    $false),
% 2.71/0.73    inference(global_subsumption,[],[f14,f1802,f1804])).
% 2.71/0.74  fof(f1804,plain,(
% 2.71/0.74    ~r1_xboole_0(sK0,sK1)),
% 2.71/0.74    inference(trivial_inequality_removal,[],[f1803])).
% 2.71/0.74  fof(f1803,plain,(
% 2.71/0.74    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) | ~r1_xboole_0(sK0,sK1)),
% 2.71/0.74    inference(forward_demodulation,[],[f1786,f38])).
% 2.71/0.74  fof(f38,plain,(
% 2.71/0.74    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.71/0.74    inference(unit_resulting_resolution,[],[f16,f21])).
% 2.71/0.74  fof(f21,plain,(
% 2.71/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f7])).
% 2.71/0.74  fof(f7,axiom,(
% 2.71/0.74    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.71/0.74  fof(f16,plain,(
% 2.71/0.74    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f5])).
% 2.71/0.74  fof(f5,axiom,(
% 2.71/0.74    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.71/0.74  fof(f1786,plain,(
% 2.71/0.74    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k1_xboole_0) | ~r1_xboole_0(sK0,sK1)),
% 2.71/0.74    inference(superposition,[],[f1686,f248])).
% 2.71/0.74  fof(f248,plain,(
% 2.71/0.74    ( ! [X6,X4,X5,X3] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) | ~r1_xboole_0(X3,X4)) )),
% 2.71/0.74    inference(forward_demodulation,[],[f247,f34])).
% 2.71/0.74  fof(f34,plain,(
% 2.71/0.74    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.71/0.74    inference(equality_resolution,[],[f23])).
% 2.71/0.74  fof(f23,plain,(
% 2.71/0.74    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f8])).
% 2.71/0.74  fof(f8,axiom,(
% 2.71/0.74    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.71/0.74  fof(f247,plain,(
% 2.71/0.74    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(k1_xboole_0,k4_xboole_0(X5,k4_xboole_0(X5,X6))) | ~r1_xboole_0(X3,X4)) )),
% 2.71/0.74    inference(forward_demodulation,[],[f226,f49])).
% 2.71/0.74  fof(f49,plain,(
% 2.71/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.71/0.74    inference(backward_demodulation,[],[f30,f38])).
% 2.71/0.74  fof(f30,plain,(
% 2.71/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.71/0.74    inference(definition_unfolding,[],[f17,f19])).
% 2.71/0.74  fof(f19,plain,(
% 2.71/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.71/0.74    inference(cnf_transformation,[],[f4])).
% 2.71/0.74  fof(f4,axiom,(
% 2.71/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.71/0.74  fof(f17,plain,(
% 2.71/0.74    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f2])).
% 2.71/0.74  fof(f2,axiom,(
% 2.71/0.74    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.71/0.74  fof(f226,plain,(
% 2.71/0.74    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(k4_xboole_0(X3,X3),k4_xboole_0(X5,k4_xboole_0(X5,X6))) | ~r1_xboole_0(X3,X4)) )),
% 2.71/0.74    inference(superposition,[],[f32,f21])).
% 2.71/0.74  fof(f32,plain,(
% 2.71/0.74    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 2.71/0.74    inference(definition_unfolding,[],[f29,f19,f19,f19])).
% 2.71/0.74  fof(f29,plain,(
% 2.71/0.74    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.71/0.74    inference(cnf_transformation,[],[f9])).
% 2.71/0.74  fof(f9,axiom,(
% 2.71/0.74    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.71/0.74  fof(f1686,plain,(
% 2.71/0.74    ( ! [X81] : (k2_zfmisc_1(sK0,sK2) != k4_xboole_0(X81,k4_xboole_0(X81,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))) )),
% 2.71/0.74    inference(superposition,[],[f71,f204])).
% 2.71/0.74  fof(f204,plain,(
% 2.71/0.74    ( ! [X6,X8,X7] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,X7))) = k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(X6,k2_xboole_0(X7,X8))))) )),
% 2.71/0.74    inference(forward_demodulation,[],[f188,f25])).
% 2.71/0.74  fof(f25,plain,(
% 2.71/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.71/0.74    inference(cnf_transformation,[],[f3])).
% 2.71/0.74  fof(f3,axiom,(
% 2.71/0.74    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.71/0.74  fof(f188,plain,(
% 2.71/0.74    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(X7,k4_xboole_0(k4_xboole_0(X6,X7),X8))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,X7)))) )),
% 2.71/0.74    inference(superposition,[],[f31,f25])).
% 2.71/0.74  fof(f31,plain,(
% 2.71/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.71/0.74    inference(definition_unfolding,[],[f18,f19,f19])).
% 2.71/0.74  fof(f18,plain,(
% 2.71/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f1])).
% 2.71/0.74  fof(f1,axiom,(
% 2.71/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.71/0.74  fof(f71,plain,(
% 2.71/0.74    ( ! [X0] : (k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_xboole_0(k2_zfmisc_1(sK1,sK3),X0))) )),
% 2.71/0.74    inference(unit_resulting_resolution,[],[f69,f20])).
% 2.71/0.74  fof(f20,plain,(
% 2.71/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f7])).
% 2.71/0.74  fof(f69,plain,(
% 2.71/0.74    ( ! [X0] : (~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_xboole_0(k2_zfmisc_1(sK1,sK3),X0))) )),
% 2.71/0.74    inference(unit_resulting_resolution,[],[f15,f26])).
% 2.71/0.74  fof(f26,plain,(
% 2.71/0.74    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f13])).
% 2.71/0.74  fof(f13,plain,(
% 2.71/0.74    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.71/0.74    inference(ennf_transformation,[],[f6])).
% 2.71/0.74  fof(f6,axiom,(
% 2.71/0.74    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.71/0.74  fof(f15,plain,(
% 2.71/0.74    ~r1_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 2.71/0.74    inference(cnf_transformation,[],[f12])).
% 2.71/0.74  fof(f12,plain,(
% 2.71/0.74    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) & (r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)))),
% 2.71/0.74    inference(ennf_transformation,[],[f11])).
% 2.71/0.74  fof(f11,negated_conjecture,(
% 2.71/0.74    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 2.71/0.74    inference(negated_conjecture,[],[f10])).
% 2.71/0.74  fof(f10,conjecture,(
% 2.71/0.74    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 2.71/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 2.71/0.74  fof(f1802,plain,(
% 2.71/0.74    ~r1_xboole_0(sK2,sK3)),
% 2.71/0.74    inference(trivial_inequality_removal,[],[f1801])).
% 2.71/0.74  fof(f1801,plain,(
% 2.71/0.74    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) | ~r1_xboole_0(sK2,sK3)),
% 2.71/0.74    inference(forward_demodulation,[],[f1785,f38])).
% 2.71/0.74  fof(f1785,plain,(
% 2.71/0.74    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k1_xboole_0) | ~r1_xboole_0(sK2,sK3)),
% 2.71/0.74    inference(superposition,[],[f1686,f257])).
% 2.71/0.74  fof(f257,plain,(
% 2.71/0.74    ( ! [X6,X4,X5,X3] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4))) | ~r1_xboole_0(X3,X4)) )),
% 2.71/0.74    inference(forward_demodulation,[],[f256,f33])).
% 2.71/0.74  fof(f33,plain,(
% 2.71/0.74    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.71/0.74    inference(equality_resolution,[],[f24])).
% 2.71/0.74  fof(f24,plain,(
% 2.71/0.74    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.71/0.74    inference(cnf_transformation,[],[f8])).
% 2.71/0.74  fof(f256,plain,(
% 2.71/0.74    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4))) = k2_zfmisc_1(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0) | ~r1_xboole_0(X3,X4)) )),
% 2.71/0.74    inference(forward_demodulation,[],[f236,f49])).
% 2.71/0.74  fof(f236,plain,(
% 2.71/0.74    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X5,X3),k4_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4))) = k2_zfmisc_1(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X3,X3)) | ~r1_xboole_0(X3,X4)) )),
% 2.71/0.74    inference(superposition,[],[f32,f21])).
% 2.71/0.74  fof(f14,plain,(
% 2.71/0.74    r1_xboole_0(sK2,sK3) | r1_xboole_0(sK0,sK1)),
% 2.71/0.74    inference(cnf_transformation,[],[f12])).
% 2.71/0.74  % SZS output end Proof for theBenchmark
% 2.71/0.74  % (670)------------------------------
% 2.71/0.74  % (670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.74  % (670)Termination reason: Refutation
% 2.71/0.74  
% 2.71/0.74  % (670)Memory used [KB]: 8571
% 2.71/0.74  % (670)Time elapsed: 0.295 s
% 2.71/0.74  % (670)------------------------------
% 2.71/0.74  % (670)------------------------------
% 2.71/0.74  % (634)Success in time 0.374 s
%------------------------------------------------------------------------------
