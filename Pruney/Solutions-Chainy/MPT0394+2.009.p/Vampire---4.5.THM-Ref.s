%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:57 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 242 expanded)
%              Number of leaves         :   15 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  114 ( 388 expanded)
%              Number of equality atoms :   60 ( 193 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1356,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1352])).

fof(f1352,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f52,f300])).

fof(f300,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(forward_demodulation,[],[f299,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f45,f47,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f299,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) ),
    inference(forward_demodulation,[],[f298,f54])).

fof(f54,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f48])).

fof(f28,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f298,plain,(
    ! [X0,X1] : k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),X1)) ),
    inference(forward_demodulation,[],[f279,f54])).

fof(f279,plain,(
    ! [X0,X1] : k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k1_setfam_1(k1_enumset1(X1,X1,X1)))) ),
    inference(unit_resulting_resolution,[],[f158,f158,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f47,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f158,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(backward_demodulation,[],[f86,f153])).

fof(f153,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f53,f148])).

fof(f148,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f114,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f114,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f100,f107])).

fof(f107,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f99,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f41,f53])).

fof(f99,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
    inference(unit_resulting_resolution,[],[f98,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f98,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f89,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f89,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f62,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f62,plain,(
    r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f53,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f100,plain,(
    ! [X0] : r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f98,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f86,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f61,f40])).

fof(f61,plain,(
    ! [X1] : ~ r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f43,f48,f48])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f52,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f26,f33,f32])).

fof(f26,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:27:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.49/0.56  % (25110)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.49/0.56  % (25117)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.49/0.56  % (25120)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.57  % (25117)Refutation not found, incomplete strategy% (25117)------------------------------
% 1.49/0.57  % (25117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (25120)Refutation not found, incomplete strategy% (25120)------------------------------
% 1.49/0.57  % (25120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (25117)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (25117)Memory used [KB]: 10618
% 1.49/0.57  % (25117)Time elapsed: 0.144 s
% 1.49/0.57  % (25117)------------------------------
% 1.49/0.57  % (25117)------------------------------
% 1.49/0.57  % (25112)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.49/0.57  % (25120)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (25120)Memory used [KB]: 1663
% 1.49/0.57  % (25120)Time elapsed: 0.123 s
% 1.49/0.57  % (25120)------------------------------
% 1.49/0.57  % (25120)------------------------------
% 1.49/0.57  % (25105)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.57  % (25104)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.57  % (25112)Refutation not found, incomplete strategy% (25112)------------------------------
% 1.49/0.57  % (25112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (25121)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.58  % (25112)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (25112)Memory used [KB]: 6140
% 1.49/0.58  % (25112)Time elapsed: 0.005 s
% 1.49/0.58  % (25112)------------------------------
% 1.49/0.58  % (25112)------------------------------
% 1.49/0.59  % (25118)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.59  % (25126)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.59  % (25105)Refutation not found, incomplete strategy% (25105)------------------------------
% 1.49/0.59  % (25105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (25105)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.59  
% 1.49/0.59  % (25105)Memory used [KB]: 10618
% 1.49/0.59  % (25105)Time elapsed: 0.160 s
% 1.49/0.59  % (25105)------------------------------
% 1.49/0.59  % (25105)------------------------------
% 1.49/0.59  % (25098)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.60  % (25101)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.49/0.60  % (25097)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.49/0.60  % (25099)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.49/0.60  % (25097)Refutation not found, incomplete strategy% (25097)------------------------------
% 1.49/0.60  % (25097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (25101)Refutation not found, incomplete strategy% (25101)------------------------------
% 1.49/0.60  % (25101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (25100)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.49/0.60  % (25101)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.60  
% 1.49/0.60  % (25101)Memory used [KB]: 6140
% 1.49/0.60  % (25101)Time elapsed: 0.169 s
% 1.49/0.60  % (25101)------------------------------
% 1.49/0.60  % (25101)------------------------------
% 1.49/0.60  % (25125)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.60  % (25102)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.49/0.60  % (25097)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.60  
% 1.49/0.60  % (25097)Memory used [KB]: 1663
% 1.49/0.60  % (25097)Time elapsed: 0.169 s
% 1.49/0.60  % (25097)------------------------------
% 1.49/0.60  % (25097)------------------------------
% 1.49/0.60  % (25111)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.49/0.60  % (25106)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.49/0.60  % (25106)Refutation not found, incomplete strategy% (25106)------------------------------
% 1.49/0.60  % (25106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (25106)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.60  
% 1.49/0.60  % (25106)Memory used [KB]: 10618
% 1.49/0.60  % (25106)Time elapsed: 0.178 s
% 1.49/0.60  % (25106)------------------------------
% 1.49/0.60  % (25106)------------------------------
% 1.49/0.61  % (25118)Refutation not found, incomplete strategy% (25118)------------------------------
% 1.49/0.61  % (25118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.61  % (25108)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.61  % (25118)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.61  
% 1.49/0.61  % (25118)Memory used [KB]: 1663
% 1.49/0.61  % (25118)Time elapsed: 0.162 s
% 1.49/0.61  % (25118)------------------------------
% 1.49/0.61  % (25118)------------------------------
% 1.49/0.61  % (25109)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.61  % (25124)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.61  % (25103)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.49/0.61  % (25122)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.61  % (25099)Refutation not found, incomplete strategy% (25099)------------------------------
% 1.49/0.61  % (25099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.61  % (25116)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.62  % (25123)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.49/0.62  % (25113)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.62  % (25119)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.62  % (25114)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.63  % (25123)Refutation not found, incomplete strategy% (25123)------------------------------
% 1.49/0.63  % (25123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.63  % (25123)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.63  
% 1.49/0.63  % (25123)Memory used [KB]: 10618
% 1.49/0.63  % (25123)Time elapsed: 0.199 s
% 1.49/0.63  % (25123)------------------------------
% 1.49/0.63  % (25123)------------------------------
% 1.49/0.63  % (25115)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.49/0.63  % (25099)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.63  
% 1.49/0.63  % (25099)Memory used [KB]: 10618
% 1.49/0.63  % (25099)Time elapsed: 0.187 s
% 1.49/0.63  % (25099)------------------------------
% 1.49/0.63  % (25099)------------------------------
% 1.49/0.63  % (25122)Refutation not found, incomplete strategy% (25122)------------------------------
% 1.49/0.63  % (25122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.63  % (25107)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.49/0.63  % (25114)Refutation not found, incomplete strategy% (25114)------------------------------
% 1.49/0.63  % (25114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.63  % (25122)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.63  
% 1.49/0.63  % (25122)Memory used [KB]: 6140
% 1.49/0.63  % (25122)Time elapsed: 0.200 s
% 1.49/0.63  % (25122)------------------------------
% 1.49/0.63  % (25122)------------------------------
% 1.49/0.63  % (25107)Refutation not found, incomplete strategy% (25107)------------------------------
% 1.49/0.63  % (25107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.63  % (25119)Refutation not found, incomplete strategy% (25119)------------------------------
% 1.49/0.63  % (25119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.63  % (25119)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.63  
% 1.49/0.63  % (25119)Memory used [KB]: 10618
% 1.49/0.63  % (25119)Time elapsed: 0.191 s
% 1.49/0.63  % (25119)------------------------------
% 1.49/0.63  % (25119)------------------------------
% 1.49/0.63  % (25108)Refutation not found, incomplete strategy% (25108)------------------------------
% 1.49/0.63  % (25108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.63  % (25108)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.63  
% 1.49/0.63  % (25108)Memory used [KB]: 10618
% 1.49/0.63  % (25108)Time elapsed: 0.210 s
% 1.49/0.63  % (25108)------------------------------
% 1.49/0.63  % (25108)------------------------------
% 1.49/0.64  % (25107)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.64  
% 1.49/0.64  % (25107)Memory used [KB]: 10618
% 1.49/0.64  % (25107)Time elapsed: 0.201 s
% 1.49/0.64  % (25107)------------------------------
% 1.49/0.64  % (25107)------------------------------
% 1.49/0.64  % (25114)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.64  
% 1.49/0.64  % (25114)Memory used [KB]: 10618
% 1.49/0.64  % (25114)Time elapsed: 0.199 s
% 1.49/0.64  % (25114)------------------------------
% 1.49/0.64  % (25114)------------------------------
% 2.25/0.67  % (25121)Refutation found. Thanks to Tanya!
% 2.25/0.67  % SZS status Theorem for theBenchmark
% 2.25/0.67  % SZS output start Proof for theBenchmark
% 2.25/0.67  fof(f1356,plain,(
% 2.25/0.67    $false),
% 2.25/0.67    inference(trivial_inequality_removal,[],[f1352])).
% 2.25/0.67  fof(f1352,plain,(
% 2.25/0.67    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.25/0.67    inference(superposition,[],[f52,f300])).
% 2.25/0.67  fof(f300,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.25/0.67    inference(forward_demodulation,[],[f299,f51])).
% 2.25/0.67  fof(f51,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 2.25/0.67    inference(definition_unfolding,[],[f44,f49])).
% 2.25/0.67  fof(f49,plain,(
% 2.25/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 2.25/0.67    inference(definition_unfolding,[],[f45,f47,f48])).
% 2.25/0.67  fof(f48,plain,(
% 2.25/0.67    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.25/0.67    inference(definition_unfolding,[],[f29,f32])).
% 2.25/0.67  fof(f32,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f11])).
% 2.25/0.67  fof(f11,axiom,(
% 2.25/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.25/0.67  fof(f29,plain,(
% 2.25/0.67    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f10])).
% 2.25/0.67  fof(f10,axiom,(
% 2.25/0.67    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.25/0.67  fof(f47,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.25/0.67    inference(definition_unfolding,[],[f31,f32])).
% 2.25/0.67  fof(f31,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f13])).
% 2.25/0.67  fof(f13,axiom,(
% 2.25/0.67    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.25/0.67  fof(f45,plain,(
% 2.25/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.25/0.67    inference(cnf_transformation,[],[f8])).
% 2.25/0.67  fof(f8,axiom,(
% 2.25/0.67    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 2.25/0.67  fof(f44,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f12])).
% 2.25/0.67  fof(f12,axiom,(
% 2.25/0.67    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.25/0.67  fof(f299,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))))) )),
% 2.25/0.67    inference(forward_demodulation,[],[f298,f54])).
% 2.25/0.67  fof(f54,plain,(
% 2.25/0.67    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 2.25/0.67    inference(definition_unfolding,[],[f28,f48])).
% 2.25/0.67  fof(f28,plain,(
% 2.25/0.67    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 2.25/0.67    inference(cnf_transformation,[],[f16])).
% 2.25/0.67  fof(f16,axiom,(
% 2.25/0.67    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.25/0.67  fof(f298,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),X1))) )),
% 2.25/0.67    inference(forward_demodulation,[],[f279,f54])).
% 2.25/0.67  fof(f279,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k1_setfam_1(k1_enumset1(X1,X1,X1))))) )),
% 2.25/0.67    inference(unit_resulting_resolution,[],[f158,f158,f59])).
% 2.25/0.67  fof(f59,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.25/0.67    inference(definition_unfolding,[],[f42,f47,f33])).
% 2.25/0.67  fof(f33,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.25/0.67    inference(cnf_transformation,[],[f6])).
% 2.25/0.67  fof(f6,axiom,(
% 2.25/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.25/0.67  fof(f42,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) )),
% 2.25/0.67    inference(cnf_transformation,[],[f24])).
% 2.25/0.67  fof(f24,plain,(
% 2.25/0.67    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.25/0.67    inference(ennf_transformation,[],[f15])).
% 2.25/0.67  fof(f15,axiom,(
% 2.25/0.67    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 2.25/0.67  fof(f158,plain,(
% 2.25/0.67    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 2.25/0.67    inference(backward_demodulation,[],[f86,f153])).
% 2.25/0.67  fof(f153,plain,(
% 2.25/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.25/0.67    inference(backward_demodulation,[],[f53,f148])).
% 2.25/0.67  fof(f148,plain,(
% 2.25/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.25/0.67    inference(unit_resulting_resolution,[],[f114,f41])).
% 2.25/0.67  fof(f41,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f7])).
% 2.25/0.67  fof(f7,axiom,(
% 2.25/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.25/0.67  fof(f114,plain,(
% 2.25/0.67    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.25/0.67    inference(backward_demodulation,[],[f100,f107])).
% 2.25/0.67  fof(f107,plain,(
% 2.25/0.67    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.25/0.67    inference(unit_resulting_resolution,[],[f99,f65])).
% 2.25/0.67  fof(f65,plain,(
% 2.25/0.67    ( ! [X0] : (~r1_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) | k1_xboole_0 = X0) )),
% 2.25/0.67    inference(superposition,[],[f41,f53])).
% 2.25/0.67  fof(f99,plain,(
% 2.25/0.67    ( ! [X0] : (r1_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X0)) )),
% 2.25/0.67    inference(unit_resulting_resolution,[],[f98,f38])).
% 2.25/0.67  fof(f38,plain,(
% 2.25/0.67    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f23])).
% 2.25/0.67  fof(f23,plain,(
% 2.25/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.25/0.67    inference(ennf_transformation,[],[f20])).
% 2.25/0.67  fof(f20,plain,(
% 2.25/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.25/0.67    inference(rectify,[],[f2])).
% 2.25/0.67  fof(f2,axiom,(
% 2.25/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.25/0.67  fof(f98,plain,(
% 2.25/0.67    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 2.25/0.67    inference(forward_demodulation,[],[f89,f56])).
% 2.25/0.67  fof(f56,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.25/0.67    inference(definition_unfolding,[],[f34,f33])).
% 2.25/0.67  fof(f34,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f5])).
% 2.25/0.67  fof(f5,axiom,(
% 2.25/0.67    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.25/0.67  fof(f89,plain,(
% 2.25/0.67    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))))) )),
% 2.25/0.67    inference(unit_resulting_resolution,[],[f62,f58])).
% 2.25/0.67  fof(f58,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.25/0.67    inference(definition_unfolding,[],[f35,f33])).
% 2.25/0.67  fof(f35,plain,(
% 2.25/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f22])).
% 2.25/0.67  fof(f22,plain,(
% 2.25/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.25/0.67    inference(ennf_transformation,[],[f19])).
% 2.25/0.67  fof(f19,plain,(
% 2.25/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.25/0.67    inference(rectify,[],[f3])).
% 2.25/0.67  fof(f3,axiom,(
% 2.25/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.25/0.67  fof(f62,plain,(
% 2.25/0.67    r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 2.25/0.67    inference(unit_resulting_resolution,[],[f53,f40])).
% 2.25/0.67  fof(f40,plain,(
% 2.25/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f7])).
% 2.25/0.67  fof(f100,plain,(
% 2.25/0.67    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 2.25/0.67    inference(unit_resulting_resolution,[],[f98,f39])).
% 2.25/0.67  fof(f39,plain,(
% 2.25/0.67    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f23])).
% 2.25/0.67  fof(f53,plain,(
% 2.25/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.25/0.67    inference(definition_unfolding,[],[f27,f33])).
% 2.25/0.67  fof(f27,plain,(
% 2.25/0.67    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.25/0.67    inference(cnf_transformation,[],[f4])).
% 2.25/0.67  fof(f4,axiom,(
% 2.25/0.67    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.25/0.67  fof(f86,plain,(
% 2.25/0.67    ( ! [X0] : (k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) )),
% 2.25/0.67    inference(unit_resulting_resolution,[],[f61,f40])).
% 2.25/0.67  fof(f61,plain,(
% 2.25/0.67    ( ! [X1] : (~r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 2.25/0.67    inference(equality_resolution,[],[f60])).
% 2.25/0.67  fof(f60,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 != X1) )),
% 2.25/0.67    inference(definition_unfolding,[],[f43,f48,f48])).
% 2.25/0.67  fof(f43,plain,(
% 2.25/0.67    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 2.25/0.67    inference(cnf_transformation,[],[f25])).
% 2.25/0.67  fof(f25,plain,(
% 2.25/0.67    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.25/0.67    inference(ennf_transformation,[],[f14])).
% 2.25/0.67  fof(f14,axiom,(
% 2.25/0.67    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 2.25/0.67  fof(f52,plain,(
% 2.25/0.67    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 2.25/0.67    inference(definition_unfolding,[],[f26,f33,f32])).
% 2.25/0.67  fof(f26,plain,(
% 2.25/0.67    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 2.25/0.67    inference(cnf_transformation,[],[f21])).
% 2.25/0.67  fof(f21,plain,(
% 2.25/0.67    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 2.25/0.67    inference(ennf_transformation,[],[f18])).
% 2.25/0.67  fof(f18,negated_conjecture,(
% 2.25/0.67    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.25/0.67    inference(negated_conjecture,[],[f17])).
% 2.25/0.67  fof(f17,conjecture,(
% 2.25/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.25/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.25/0.67  % SZS output end Proof for theBenchmark
% 2.25/0.67  % (25121)------------------------------
% 2.25/0.67  % (25121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.67  % (25121)Termination reason: Refutation
% 2.25/0.67  
% 2.25/0.67  % (25121)Memory used [KB]: 6780
% 2.25/0.67  % (25121)Time elapsed: 0.185 s
% 2.25/0.67  % (25121)------------------------------
% 2.25/0.67  % (25121)------------------------------
% 2.25/0.68  % (25096)Success in time 0.302 s
%------------------------------------------------------------------------------
