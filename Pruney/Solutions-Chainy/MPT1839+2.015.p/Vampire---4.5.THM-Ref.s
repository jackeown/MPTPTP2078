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
% DateTime   : Thu Dec  3 13:20:03 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 266 expanded)
%              Number of leaves         :   15 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  165 ( 474 expanded)
%              Number of equality atoms :   62 ( 196 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(subsumption_resolution,[],[f376,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f63,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f45,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f63,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f61,f29])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(backward_demodulation,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f51])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f376,plain,(
    ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f25,f375])).

fof(f375,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f374,f78])).

fof(f78,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f46,f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f374,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f350,f67])).

fof(f350,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f137,f342])).

fof(f342,plain,(
    ! [X22] :
      ( sK0 = k4_xboole_0(sK0,X22)
      | k1_xboole_0 = k4_xboole_0(sK0,X22) ) ),
    inference(resolution,[],[f286,f82])).

fof(f82,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f41,f70])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f286,plain,(
    ! [X15,X16] :
      ( r1_tarski(k4_xboole_0(sK0,X15),X16)
      | sK0 = k4_xboole_0(sK0,X15) ) ),
    inference(trivial_inequality_removal,[],[f285])).

fof(f285,plain,(
    ! [X15,X16] :
      ( k1_xboole_0 != k1_xboole_0
      | sK0 = k4_xboole_0(sK0,X15)
      | r1_tarski(k4_xboole_0(sK0,X15),X16) ) ),
    inference(superposition,[],[f167,f243])).

fof(f243,plain,(
    ! [X12,X11] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X11,X12),X11) ),
    inference(resolution,[],[f229,f45])).

fof(f229,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f221,f58])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k4_xboole_0(X0,X1))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f57,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f56,f55])).

fof(f56,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f38,f50,f51])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f35,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f167,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,sK0)
      | sK0 = X1
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f156,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_xboole_0 != k4_xboole_0(X0,sK0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f124,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f124,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | sK0 = X1
      | k1_xboole_0 != k4_xboole_0(X1,sK0) ) ),
    inference(resolution,[],[f120,f46])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | v1_xboole_0(X0)
      | sK0 = X0 ) ),
    inference(subsumption_resolution,[],[f119,f26])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(f119,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f30,f27])).

fof(f27,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f137,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f135,f60])).

fof(f60,plain,(
    ~ v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f52,f55])).

fof(f52,plain,(
    ~ v1_xboole_0(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f24,f51])).

fof(f24,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f135,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 != X1 ) ),
    inference(forward_demodulation,[],[f133,f29])).

fof(f133,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK0
      | v1_xboole_0(X1)
      | k1_xboole_0 != k4_xboole_0(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f128,f46])).

fof(f128,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = sK0
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f125,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0),X1)
      | ~ r1_tarski(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f42,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f123,f32])).

% (29086)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f123,plain,
    ( v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f120,f70])).

fof(f25,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:25:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (29071)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (29097)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (29081)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (29081)Refutation not found, incomplete strategy% (29081)------------------------------
% 0.21/0.52  % (29081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29081)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29081)Memory used [KB]: 10618
% 0.21/0.52  % (29081)Time elapsed: 0.118 s
% 0.21/0.52  % (29081)------------------------------
% 0.21/0.52  % (29081)------------------------------
% 0.21/0.52  % (29072)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (29095)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (29072)Refutation not found, incomplete strategy% (29072)------------------------------
% 0.21/0.52  % (29072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29072)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29072)Memory used [KB]: 10618
% 0.21/0.52  % (29072)Time elapsed: 0.116 s
% 0.21/0.52  % (29072)------------------------------
% 0.21/0.52  % (29072)------------------------------
% 0.21/0.53  % (29077)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (29073)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (29076)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (29074)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (29096)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (29094)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (29088)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.54  % (29099)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  % (29070)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.42/0.55  % (29085)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (29092)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.55  % (29070)Refutation not found, incomplete strategy% (29070)------------------------------
% 1.42/0.55  % (29070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (29070)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (29070)Memory used [KB]: 1663
% 1.42/0.55  % (29070)Time elapsed: 0.135 s
% 1.42/0.55  % (29070)------------------------------
% 1.42/0.55  % (29070)------------------------------
% 1.42/0.55  % (29080)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  % (29092)Refutation not found, incomplete strategy% (29092)------------------------------
% 1.42/0.55  % (29092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (29092)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (29092)Memory used [KB]: 10746
% 1.42/0.55  % (29092)Time elapsed: 0.103 s
% 1.42/0.55  % (29092)------------------------------
% 1.42/0.55  % (29092)------------------------------
% 1.42/0.55  % (29080)Refutation not found, incomplete strategy% (29080)------------------------------
% 1.42/0.55  % (29080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (29080)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (29080)Memory used [KB]: 10618
% 1.42/0.55  % (29080)Time elapsed: 0.141 s
% 1.42/0.55  % (29080)------------------------------
% 1.42/0.55  % (29080)------------------------------
% 1.42/0.55  % (29087)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.55  % (29093)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.55  % (29083)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.55  % (29098)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.55  % (29091)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.56  % (29079)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.56  % (29076)Refutation found. Thanks to Tanya!
% 1.42/0.56  % SZS status Theorem for theBenchmark
% 1.42/0.56  % SZS output start Proof for theBenchmark
% 1.42/0.56  fof(f412,plain,(
% 1.42/0.56    $false),
% 1.42/0.56    inference(subsumption_resolution,[],[f376,f70])).
% 1.42/0.56  fof(f70,plain,(
% 1.42/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.42/0.56    inference(backward_demodulation,[],[f63,f67])).
% 1.42/0.56  fof(f67,plain,(
% 1.42/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.42/0.56    inference(resolution,[],[f45,f58])).
% 1.42/0.56  fof(f58,plain,(
% 1.42/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.42/0.56    inference(equality_resolution,[],[f40])).
% 1.42/0.56  fof(f40,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.42/0.56    inference(cnf_transformation,[],[f3])).
% 1.42/0.56  fof(f3,axiom,(
% 1.42/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.56  fof(f45,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.42/0.56    inference(cnf_transformation,[],[f4])).
% 1.42/0.56  fof(f4,axiom,(
% 1.42/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.42/0.56  fof(f63,plain,(
% 1.42/0.56    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,X0),X0)) )),
% 1.42/0.56    inference(superposition,[],[f61,f29])).
% 1.42/0.56  fof(f29,plain,(
% 1.42/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.56    inference(cnf_transformation,[],[f8])).
% 1.42/0.56  fof(f8,axiom,(
% 1.42/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.42/0.56  fof(f61,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.42/0.56    inference(backward_demodulation,[],[f54,f55])).
% 1.42/0.56  fof(f55,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f37,f51])).
% 1.42/0.56  fof(f51,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f34,f49])).
% 1.42/0.56  fof(f49,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.42/0.56    inference(definition_unfolding,[],[f36,f47])).
% 1.42/0.56  fof(f47,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f12])).
% 1.42/0.56  fof(f12,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.42/0.56  fof(f36,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f11])).
% 1.42/0.56  fof(f11,axiom,(
% 1.42/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.56  fof(f34,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f14])).
% 1.42/0.56  fof(f14,axiom,(
% 1.42/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.42/0.56  fof(f37,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f9])).
% 1.42/0.56  fof(f9,axiom,(
% 1.42/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.42/0.56  fof(f54,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 1.42/0.56    inference(definition_unfolding,[],[f33,f51])).
% 1.42/0.56  fof(f33,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f6])).
% 1.42/0.56  fof(f6,axiom,(
% 1.42/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.42/0.56  fof(f376,plain,(
% 1.42/0.56    ~r1_tarski(k1_xboole_0,sK1)),
% 1.42/0.56    inference(backward_demodulation,[],[f25,f375])).
% 1.42/0.56  fof(f375,plain,(
% 1.42/0.56    k1_xboole_0 = sK0),
% 1.42/0.56    inference(subsumption_resolution,[],[f374,f78])).
% 1.42/0.56  fof(f78,plain,(
% 1.42/0.56    k1_xboole_0 != k4_xboole_0(sK0,sK1)),
% 1.42/0.56    inference(resolution,[],[f46,f25])).
% 1.42/0.56  fof(f46,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.42/0.56    inference(cnf_transformation,[],[f4])).
% 1.42/0.56  fof(f374,plain,(
% 1.42/0.56    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.42/0.56    inference(subsumption_resolution,[],[f350,f67])).
% 1.42/0.56  fof(f350,plain,(
% 1.42/0.56    k1_xboole_0 != k4_xboole_0(sK0,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.42/0.56    inference(superposition,[],[f137,f342])).
% 1.42/0.56  fof(f342,plain,(
% 1.42/0.56    ( ! [X22] : (sK0 = k4_xboole_0(sK0,X22) | k1_xboole_0 = k4_xboole_0(sK0,X22)) )),
% 1.42/0.56    inference(resolution,[],[f286,f82])).
% 1.42/0.56  fof(f82,plain,(
% 1.42/0.56    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 1.42/0.56    inference(resolution,[],[f41,f70])).
% 1.42/0.56  fof(f41,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.42/0.56    inference(cnf_transformation,[],[f3])).
% 1.42/0.56  fof(f286,plain,(
% 1.42/0.56    ( ! [X15,X16] : (r1_tarski(k4_xboole_0(sK0,X15),X16) | sK0 = k4_xboole_0(sK0,X15)) )),
% 1.42/0.56    inference(trivial_inequality_removal,[],[f285])).
% 1.42/0.56  fof(f285,plain,(
% 1.42/0.56    ( ! [X15,X16] : (k1_xboole_0 != k1_xboole_0 | sK0 = k4_xboole_0(sK0,X15) | r1_tarski(k4_xboole_0(sK0,X15),X16)) )),
% 1.42/0.56    inference(superposition,[],[f167,f243])).
% 1.42/0.56  fof(f243,plain,(
% 1.42/0.56    ( ! [X12,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X11,X12),X11)) )),
% 1.42/0.56    inference(resolution,[],[f229,f45])).
% 1.42/0.56  fof(f229,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.42/0.56    inference(resolution,[],[f221,f58])).
% 1.42/0.56  fof(f221,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X2,k4_xboole_0(X0,X1)) | r1_tarski(X2,X0)) )),
% 1.42/0.56    inference(superposition,[],[f57,f62])).
% 1.42/0.56  fof(f62,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 1.42/0.56    inference(forward_demodulation,[],[f56,f55])).
% 1.42/0.56  fof(f56,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k4_xboole_0(X0,X1))) = X0) )),
% 1.42/0.56    inference(definition_unfolding,[],[f38,f50,f51])).
% 1.42/0.56  fof(f50,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f35,f49])).
% 1.42/0.56  fof(f35,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f13])).
% 1.42/0.56  fof(f13,axiom,(
% 1.42/0.56    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.42/0.56  fof(f38,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.42/0.56    inference(cnf_transformation,[],[f10])).
% 1.42/0.56  fof(f10,axiom,(
% 1.42/0.56    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.42/0.56  fof(f57,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.42/0.56    inference(definition_unfolding,[],[f48,f50])).
% 1.42/0.56  fof(f48,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f23])).
% 1.42/0.56  fof(f23,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.42/0.56    inference(ennf_transformation,[],[f5])).
% 1.42/0.56  fof(f5,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.42/0.56  fof(f167,plain,(
% 1.42/0.56    ( ! [X2,X1] : (k1_xboole_0 != k4_xboole_0(X1,sK0) | sK0 = X1 | r1_tarski(X1,X2)) )),
% 1.42/0.56    inference(resolution,[],[f156,f43])).
% 1.42/0.56  fof(f43,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f22])).
% 1.42/0.56  fof(f22,plain,(
% 1.42/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f2])).
% 1.42/0.56  fof(f2,axiom,(
% 1.42/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.42/0.56  fof(f156,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_xboole_0 != k4_xboole_0(X0,sK0) | sK0 = X0) )),
% 1.42/0.56    inference(resolution,[],[f124,f32])).
% 1.42/0.56  fof(f32,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f1])).
% 1.42/0.56  fof(f1,axiom,(
% 1.42/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.42/0.56  fof(f124,plain,(
% 1.42/0.56    ( ! [X1] : (v1_xboole_0(X1) | sK0 = X1 | k1_xboole_0 != k4_xboole_0(X1,sK0)) )),
% 1.42/0.56    inference(resolution,[],[f120,f46])).
% 1.42/0.56  fof(f120,plain,(
% 1.42/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0) )),
% 1.42/0.56    inference(subsumption_resolution,[],[f119,f26])).
% 1.42/0.56  fof(f26,plain,(
% 1.42/0.56    ~v1_xboole_0(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f19])).
% 1.42/0.56  fof(f19,plain,(
% 1.42/0.56    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 1.42/0.56    inference(flattening,[],[f18])).
% 1.42/0.56  fof(f18,plain,(
% 1.42/0.56    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 1.42/0.56    inference(ennf_transformation,[],[f17])).
% 1.42/0.56  fof(f17,negated_conjecture,(
% 1.42/0.56    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.42/0.56    inference(negated_conjecture,[],[f16])).
% 1.42/0.56  fof(f16,conjecture,(
% 1.42/0.56    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).
% 1.42/0.56  fof(f119,plain,(
% 1.42/0.56    ( ! [X0] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | ~r1_tarski(X0,sK0) | sK0 = X0) )),
% 1.42/0.56    inference(resolution,[],[f30,f27])).
% 1.42/0.56  fof(f27,plain,(
% 1.42/0.56    v1_zfmisc_1(sK0)),
% 1.42/0.56    inference(cnf_transformation,[],[f19])).
% 1.42/0.56  fof(f30,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.42/0.56    inference(cnf_transformation,[],[f21])).
% 1.42/0.56  fof(f21,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.42/0.56    inference(flattening,[],[f20])).
% 1.42/0.56  fof(f20,plain,(
% 1.42/0.56    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.42/0.56    inference(ennf_transformation,[],[f15])).
% 1.42/0.56  fof(f15,axiom,(
% 1.42/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.42/0.56  fof(f137,plain,(
% 1.42/0.56    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK0),
% 1.42/0.56    inference(resolution,[],[f135,f60])).
% 1.42/0.56  fof(f60,plain,(
% 1.42/0.56    ~v1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.42/0.56    inference(backward_demodulation,[],[f52,f55])).
% 1.42/0.56  fof(f52,plain,(
% 1.42/0.56    ~v1_xboole_0(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.42/0.56    inference(definition_unfolding,[],[f24,f51])).
% 1.42/0.56  fof(f24,plain,(
% 1.42/0.56    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 1.42/0.56    inference(cnf_transformation,[],[f19])).
% 1.42/0.56  fof(f135,plain,(
% 1.42/0.56    ( ! [X1] : (v1_xboole_0(X1) | k1_xboole_0 = sK0 | k1_xboole_0 != X1) )),
% 1.42/0.56    inference(forward_demodulation,[],[f133,f29])).
% 1.42/0.56  fof(f133,plain,(
% 1.42/0.56    ( ! [X1] : (k1_xboole_0 = sK0 | v1_xboole_0(X1) | k1_xboole_0 != k4_xboole_0(X1,k1_xboole_0)) )),
% 1.42/0.56    inference(resolution,[],[f128,f46])).
% 1.42/0.56  fof(f128,plain,(
% 1.42/0.56    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = sK0 | v1_xboole_0(X1)) )),
% 1.42/0.56    inference(resolution,[],[f125,f91])).
% 1.42/0.56  fof(f91,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0),X1) | ~r1_tarski(X0,X1) | v1_xboole_0(X0)) )),
% 1.42/0.56    inference(resolution,[],[f42,f31])).
% 1.42/0.56  fof(f31,plain,(
% 1.42/0.56    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f1])).
% 1.42/0.56  fof(f42,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f22])).
% 1.42/0.56  fof(f125,plain,(
% 1.42/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = sK0) )),
% 1.42/0.56    inference(resolution,[],[f123,f32])).
% 1.42/0.56  % (29086)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.56  fof(f123,plain,(
% 1.42/0.56    v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0),
% 1.42/0.56    inference(resolution,[],[f120,f70])).
% 1.42/0.56  fof(f25,plain,(
% 1.42/0.56    ~r1_tarski(sK0,sK1)),
% 1.42/0.56    inference(cnf_transformation,[],[f19])).
% 1.42/0.56  % SZS output end Proof for theBenchmark
% 1.42/0.56  % (29076)------------------------------
% 1.42/0.56  % (29076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (29076)Termination reason: Refutation
% 1.42/0.56  
% 1.42/0.56  % (29076)Memory used [KB]: 6396
% 1.42/0.56  % (29076)Time elapsed: 0.130 s
% 1.42/0.56  % (29076)------------------------------
% 1.42/0.56  % (29076)------------------------------
% 1.42/0.56  % (29069)Success in time 0.196 s
%------------------------------------------------------------------------------
