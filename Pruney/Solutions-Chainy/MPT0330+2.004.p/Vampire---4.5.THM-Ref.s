%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:59 EST 2020

% Result     : Theorem 7.67s
% Output     : Refutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 453 expanded)
%              Number of leaves         :   16 ( 150 expanded)
%              Depth                    :   17
%              Number of atoms          :  130 ( 588 expanded)
%              Number of equality atoms :   35 ( 338 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8771,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4497,f8693,f8770])).

fof(f8770,plain,(
    spl6_22 ),
    inference(avatar_contradiction_clause,[],[f8764])).

fof(f8764,plain,
    ( $false
    | spl6_22 ),
    inference(unit_resulting_resolution,[],[f34,f591,f4496,f8455])).

fof(f8455,plain,(
    ! [X35,X33,X34] :
      ( ~ r1_tarski(X34,X33)
      | r1_tarski(X34,X35)
      | ~ r1_tarski(X33,X35) ) ),
    inference(superposition,[],[f191,f934])).

fof(f934,plain,(
    ! [X17,X16] :
      ( k3_tarski(k1_enumset1(X17,X17,X16)) = X17
      | ~ r1_tarski(X16,X17) ) ),
    inference(forward_demodulation,[],[f874,f352])).

fof(f352,plain,(
    ! [X11] : k5_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(forward_demodulation,[],[f313,f59])).

fof(f59,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f313,plain,(
    ! [X11] : k5_xboole_0(X11,k1_xboole_0) = k3_tarski(k1_enumset1(X11,X11,X11)) ),
    inference(superposition,[],[f62,f302])).

fof(f302,plain,(
    ! [X13] : k1_xboole_0 = k4_xboole_0(X13,X13) ),
    inference(resolution,[],[f284,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f284,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f65,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f57])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f57])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f874,plain,(
    ! [X17,X16] :
      ( k3_tarski(k1_enumset1(X17,X17,X16)) = k5_xboole_0(X17,k1_xboole_0)
      | ~ r1_tarski(X16,X17) ) ),
    inference(superposition,[],[f62,f715])).

fof(f715,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 = k4_xboole_0(X6,X7)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f685,f84])).

fof(f685,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X3,X2),k1_xboole_0)
      | ~ r1_tarski(X3,X2) ) ),
    inference(superposition,[],[f65,f661])).

fof(f661,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f660,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f40,f41,f41])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f660,plain,(
    ! [X0] : k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(forward_demodulation,[],[f257,f352])).

fof(f257,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) ),
    inference(superposition,[],[f256,f61])).

fof(f256,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f62,f111])).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f84,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X0)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f66,f61])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f4496,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f4494])).

fof(f4494,plain,
    ( spl6_22
  <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f591,plain,(
    ! [X30,X31,X29] : r1_tarski(k2_zfmisc_1(X31,X30),k2_zfmisc_1(k3_tarski(k1_enumset1(X29,X29,X31)),X30)) ),
    inference(superposition,[],[f155,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f48,f57,f57])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f155,plain,(
    ! [X2,X1] : r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(superposition,[],[f60,f61])).

fof(f34,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f8693,plain,(
    spl6_21 ),
    inference(avatar_contradiction_clause,[],[f8632])).

fof(f8632,plain,
    ( $false
    | spl6_21 ),
    inference(unit_resulting_resolution,[],[f4492,f585,f33,f8455])).

fof(f33,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f585,plain,(
    ! [X6,X4,X5] : r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(k3_tarski(k1_enumset1(X4,X4,X6)),X5)) ),
    inference(superposition,[],[f60,f64])).

fof(f4492,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f4490])).

fof(f4490,plain,
    ( spl6_21
  <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f4497,plain,
    ( ~ spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f4453,f4494,f4490])).

fof(f4453,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) ),
    inference(resolution,[],[f512,f58])).

fof(f58,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f35,f57,f57,f57])).

fof(f35,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f22])).

fof(f512,plain,(
    ! [X21,X19,X22,X20,X18] :
      ( r1_tarski(k3_tarski(k1_enumset1(X21,X21,X22)),k2_zfmisc_1(X18,k3_tarski(k1_enumset1(X19,X19,X20))))
      | ~ r1_tarski(X22,k2_zfmisc_1(X18,X20))
      | ~ r1_tarski(X21,k2_zfmisc_1(X18,X19)) ) ),
    inference(superposition,[],[f67,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f49,f57,f57])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f57,f57])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:23:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (10808)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (10813)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (10832)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (10807)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (10816)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (10806)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (10812)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (10831)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (10804)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (10824)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (10809)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (10821)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (10815)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (10821)Refutation not found, incomplete strategy% (10821)------------------------------
% 0.20/0.54  % (10821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10821)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10821)Memory used [KB]: 1791
% 0.20/0.54  % (10821)Time elapsed: 0.123 s
% 0.20/0.54  % (10821)------------------------------
% 0.20/0.54  % (10821)------------------------------
% 0.20/0.54  % (10818)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (10818)Refutation not found, incomplete strategy% (10818)------------------------------
% 0.20/0.54  % (10818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10818)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10818)Memory used [KB]: 1663
% 0.20/0.54  % (10818)Time elapsed: 0.099 s
% 0.20/0.54  % (10818)------------------------------
% 0.20/0.54  % (10818)------------------------------
% 0.20/0.54  % (10827)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (10826)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (10805)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.55  % (10823)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (10833)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (10805)Refutation not found, incomplete strategy% (10805)------------------------------
% 0.20/0.55  % (10805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10805)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10805)Memory used [KB]: 1663
% 0.20/0.55  % (10805)Time elapsed: 0.135 s
% 0.20/0.55  % (10805)------------------------------
% 0.20/0.55  % (10805)------------------------------
% 0.20/0.55  % (10819)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (10811)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (10832)Refutation not found, incomplete strategy% (10832)------------------------------
% 0.20/0.55  % (10832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10832)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10832)Memory used [KB]: 10746
% 0.20/0.55  % (10832)Time elapsed: 0.144 s
% 0.20/0.55  % (10832)------------------------------
% 0.20/0.55  % (10832)------------------------------
% 0.20/0.55  % (10814)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (10829)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (10825)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (10814)Refutation not found, incomplete strategy% (10814)------------------------------
% 0.20/0.55  % (10814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (10814)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (10814)Memory used [KB]: 10746
% 0.20/0.55  % (10814)Time elapsed: 0.131 s
% 0.20/0.55  % (10814)------------------------------
% 0.20/0.55  % (10814)------------------------------
% 0.20/0.56  % (10822)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (10828)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.56  % (10820)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.56  % (10820)Refutation not found, incomplete strategy% (10820)------------------------------
% 0.20/0.56  % (10820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (10820)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (10820)Memory used [KB]: 10618
% 0.20/0.56  % (10820)Time elapsed: 0.149 s
% 0.20/0.56  % (10820)------------------------------
% 0.20/0.56  % (10820)------------------------------
% 0.20/0.56  % (10817)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.56  % (10810)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (10830)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.17/0.65  % (10844)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.29/0.66  % (10807)Refutation not found, incomplete strategy% (10807)------------------------------
% 2.29/0.66  % (10807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.67  % (10807)Termination reason: Refutation not found, incomplete strategy
% 2.29/0.67  
% 2.29/0.67  % (10807)Memory used [KB]: 6140
% 2.29/0.67  % (10807)Time elapsed: 0.240 s
% 2.29/0.67  % (10807)------------------------------
% 2.29/0.67  % (10807)------------------------------
% 2.29/0.67  % (10846)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.29/0.69  % (10848)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.29/0.70  % (10845)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.67/0.72  % (10848)Refutation not found, incomplete strategy% (10848)------------------------------
% 2.67/0.72  % (10848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.67/0.72  % (10848)Termination reason: Refutation not found, incomplete strategy
% 2.67/0.72  
% 2.67/0.72  % (10848)Memory used [KB]: 10746
% 2.67/0.72  % (10848)Time elapsed: 0.115 s
% 2.67/0.72  % (10848)------------------------------
% 2.67/0.72  % (10848)------------------------------
% 2.67/0.73  % (10847)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.67/0.74  % (10849)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.98/0.80  % (10850)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.98/0.81  % (10806)Time limit reached!
% 2.98/0.81  % (10806)------------------------------
% 2.98/0.81  % (10806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.83  % (10828)Time limit reached!
% 2.98/0.83  % (10828)------------------------------
% 2.98/0.83  % (10828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.83  % (10828)Termination reason: Time limit
% 2.98/0.83  
% 2.98/0.83  % (10828)Memory used [KB]: 12537
% 2.98/0.83  % (10828)Time elapsed: 0.418 s
% 2.98/0.83  % (10828)------------------------------
% 2.98/0.83  % (10828)------------------------------
% 2.98/0.83  % (10806)Termination reason: Time limit
% 2.98/0.83  % (10806)Termination phase: Saturation
% 2.98/0.83  
% 2.98/0.83  % (10806)Memory used [KB]: 8059
% 2.98/0.83  % (10806)Time elapsed: 0.400 s
% 2.98/0.83  % (10806)------------------------------
% 2.98/0.83  % (10806)------------------------------
% 3.58/0.86  % (10851)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.93/0.93  % (10833)Time limit reached!
% 3.93/0.93  % (10833)------------------------------
% 3.93/0.93  % (10833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.93  % (10833)Termination reason: Time limit
% 3.93/0.93  
% 3.93/0.93  % (10833)Memory used [KB]: 2046
% 3.93/0.93  % (10833)Time elapsed: 0.516 s
% 3.93/0.93  % (10833)------------------------------
% 3.93/0.93  % (10833)------------------------------
% 3.93/0.93  % (10853)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.93/0.93  % (10852)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 4.32/0.95  % (10810)Time limit reached!
% 4.32/0.95  % (10810)------------------------------
% 4.32/0.95  % (10810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/0.95  % (10810)Termination reason: Time limit
% 4.32/0.95  
% 4.32/0.95  % (10810)Memory used [KB]: 13688
% 4.32/0.95  % (10810)Time elapsed: 0.502 s
% 4.32/0.95  % (10810)------------------------------
% 4.32/0.95  % (10810)------------------------------
% 4.94/1.06  % (10811)Time limit reached!
% 4.94/1.06  % (10811)------------------------------
% 4.94/1.06  % (10811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/1.06  % (10811)Termination reason: Time limit
% 4.94/1.06  
% 4.94/1.06  % (10811)Memory used [KB]: 6140
% 4.94/1.06  % (10811)Time elapsed: 0.629 s
% 4.94/1.06  % (10811)------------------------------
% 4.94/1.06  % (10811)------------------------------
% 4.94/1.07  % (10854)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.94/1.11  % (10855)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 6.06/1.19  % (10856)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 7.67/1.35  % (10817)Refutation found. Thanks to Tanya!
% 7.67/1.35  % SZS status Theorem for theBenchmark
% 7.67/1.35  % SZS output start Proof for theBenchmark
% 7.67/1.35  fof(f8771,plain,(
% 7.67/1.35    $false),
% 7.67/1.35    inference(avatar_sat_refutation,[],[f4497,f8693,f8770])).
% 7.67/1.35  fof(f8770,plain,(
% 7.67/1.35    spl6_22),
% 7.67/1.35    inference(avatar_contradiction_clause,[],[f8764])).
% 7.67/1.35  fof(f8764,plain,(
% 7.67/1.35    $false | spl6_22),
% 7.67/1.35    inference(unit_resulting_resolution,[],[f34,f591,f4496,f8455])).
% 7.67/1.35  fof(f8455,plain,(
% 7.67/1.35    ( ! [X35,X33,X34] : (~r1_tarski(X34,X33) | r1_tarski(X34,X35) | ~r1_tarski(X33,X35)) )),
% 7.67/1.35    inference(superposition,[],[f191,f934])).
% 7.67/1.35  fof(f934,plain,(
% 7.67/1.35    ( ! [X17,X16] : (k3_tarski(k1_enumset1(X17,X17,X16)) = X17 | ~r1_tarski(X16,X17)) )),
% 7.67/1.35    inference(forward_demodulation,[],[f874,f352])).
% 7.67/1.35  fof(f352,plain,(
% 7.67/1.35    ( ! [X11] : (k5_xboole_0(X11,k1_xboole_0) = X11) )),
% 7.67/1.35    inference(forward_demodulation,[],[f313,f59])).
% 7.67/1.35  fof(f59,plain,(
% 7.67/1.35    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 7.67/1.35    inference(definition_unfolding,[],[f37,f57])).
% 7.67/1.35  fof(f57,plain,(
% 7.67/1.35    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 7.67/1.35    inference(definition_unfolding,[],[f42,f41])).
% 7.67/1.35  fof(f41,plain,(
% 7.67/1.35    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.67/1.35    inference(cnf_transformation,[],[f15])).
% 7.67/1.35  fof(f15,axiom,(
% 7.67/1.35    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 7.67/1.35  fof(f42,plain,(
% 7.67/1.35    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.67/1.35    inference(cnf_transformation,[],[f16])).
% 7.67/1.35  fof(f16,axiom,(
% 7.67/1.35    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 7.67/1.35  fof(f37,plain,(
% 7.67/1.35    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.67/1.35    inference(cnf_transformation,[],[f20])).
% 7.67/1.35  fof(f20,plain,(
% 7.67/1.35    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.67/1.35    inference(rectify,[],[f1])).
% 7.67/1.35  fof(f1,axiom,(
% 7.67/1.35    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 7.67/1.35  fof(f313,plain,(
% 7.67/1.35    ( ! [X11] : (k5_xboole_0(X11,k1_xboole_0) = k3_tarski(k1_enumset1(X11,X11,X11))) )),
% 7.67/1.35    inference(superposition,[],[f62,f302])).
% 7.67/1.35  fof(f302,plain,(
% 7.67/1.35    ( ! [X13] : (k1_xboole_0 = k4_xboole_0(X13,X13)) )),
% 7.67/1.35    inference(resolution,[],[f284,f84])).
% 7.67/1.35  fof(f84,plain,(
% 7.67/1.35    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 7.67/1.35    inference(resolution,[],[f47,f36])).
% 7.67/1.35  fof(f36,plain,(
% 7.67/1.35    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.67/1.35    inference(cnf_transformation,[],[f7])).
% 7.67/1.35  fof(f7,axiom,(
% 7.67/1.35    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 7.67/1.35  fof(f47,plain,(
% 7.67/1.35    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 7.67/1.35    inference(cnf_transformation,[],[f3])).
% 7.67/1.35  fof(f3,axiom,(
% 7.67/1.35    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.67/1.35  fof(f284,plain,(
% 7.67/1.35    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 7.67/1.35    inference(resolution,[],[f65,f60])).
% 7.67/1.35  fof(f60,plain,(
% 7.67/1.35    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 7.67/1.35    inference(definition_unfolding,[],[f38,f57])).
% 7.67/1.35  fof(f38,plain,(
% 7.67/1.35    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.67/1.35    inference(cnf_transformation,[],[f11])).
% 7.67/1.35  fof(f11,axiom,(
% 7.67/1.35    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 7.67/1.35  fof(f65,plain,(
% 7.67/1.35    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.67/1.35    inference(definition_unfolding,[],[f52,f57])).
% 7.67/1.35  fof(f52,plain,(
% 7.67/1.35    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.67/1.35    inference(cnf_transformation,[],[f25])).
% 7.67/1.35  fof(f25,plain,(
% 7.67/1.35    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.67/1.35    inference(ennf_transformation,[],[f9])).
% 7.67/1.35  fof(f9,axiom,(
% 7.67/1.35    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 7.67/1.35  fof(f62,plain,(
% 7.67/1.35    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 7.67/1.35    inference(definition_unfolding,[],[f43,f57])).
% 7.67/1.35  fof(f43,plain,(
% 7.67/1.35    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.67/1.35    inference(cnf_transformation,[],[f13])).
% 7.67/1.35  fof(f13,axiom,(
% 7.67/1.35    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 7.67/1.35  fof(f874,plain,(
% 7.67/1.35    ( ! [X17,X16] : (k3_tarski(k1_enumset1(X17,X17,X16)) = k5_xboole_0(X17,k1_xboole_0) | ~r1_tarski(X16,X17)) )),
% 7.67/1.35    inference(superposition,[],[f62,f715])).
% 7.67/1.35  fof(f715,plain,(
% 7.67/1.35    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(X6,X7) | ~r1_tarski(X6,X7)) )),
% 7.67/1.35    inference(resolution,[],[f685,f84])).
% 7.67/1.35  fof(f685,plain,(
% 7.67/1.35    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,X2),k1_xboole_0) | ~r1_tarski(X3,X2)) )),
% 7.67/1.35    inference(superposition,[],[f65,f661])).
% 7.67/1.35  fof(f661,plain,(
% 7.67/1.35    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 7.67/1.35    inference(superposition,[],[f660,f61])).
% 7.67/1.35  fof(f61,plain,(
% 7.67/1.35    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 7.67/1.35    inference(definition_unfolding,[],[f40,f41,f41])).
% 7.67/1.35  fof(f40,plain,(
% 7.67/1.35    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.67/1.35    inference(cnf_transformation,[],[f14])).
% 7.67/1.35  fof(f14,axiom,(
% 7.67/1.35    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 7.67/1.35  fof(f660,plain,(
% 7.67/1.35    ( ! [X0] : (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 7.67/1.35    inference(forward_demodulation,[],[f257,f352])).
% 7.67/1.35  fof(f257,plain,(
% 7.67/1.35    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) )),
% 7.67/1.35    inference(superposition,[],[f256,f61])).
% 7.67/1.35  fof(f256,plain,(
% 7.67/1.35    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0)) )),
% 7.67/1.35    inference(superposition,[],[f62,f111])).
% 7.67/1.35  fof(f111,plain,(
% 7.67/1.35    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 7.67/1.35    inference(resolution,[],[f84,f39])).
% 7.67/1.35  fof(f39,plain,(
% 7.67/1.35    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.67/1.35    inference(cnf_transformation,[],[f8])).
% 7.67/1.35  fof(f8,axiom,(
% 7.67/1.35    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 7.67/1.35  fof(f191,plain,(
% 7.67/1.35    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X0)),X2) | r1_tarski(X0,X2)) )),
% 7.67/1.35    inference(superposition,[],[f66,f61])).
% 7.67/1.35  fof(f66,plain,(
% 7.67/1.35    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 7.67/1.35    inference(definition_unfolding,[],[f53,f57])).
% 7.67/1.35  fof(f53,plain,(
% 7.67/1.35    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 7.67/1.35    inference(cnf_transformation,[],[f26])).
% 7.67/1.35  fof(f26,plain,(
% 7.67/1.35    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.67/1.35    inference(ennf_transformation,[],[f5])).
% 7.67/1.35  fof(f5,axiom,(
% 7.67/1.35    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 7.67/1.35  fof(f4496,plain,(
% 7.67/1.35    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5)) | spl6_22),
% 7.67/1.35    inference(avatar_component_clause,[],[f4494])).
% 7.67/1.35  fof(f4494,plain,(
% 7.67/1.35    spl6_22 <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5))),
% 7.67/1.35    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 7.67/1.35  fof(f591,plain,(
% 7.67/1.35    ( ! [X30,X31,X29] : (r1_tarski(k2_zfmisc_1(X31,X30),k2_zfmisc_1(k3_tarski(k1_enumset1(X29,X29,X31)),X30))) )),
% 7.67/1.35    inference(superposition,[],[f155,f64])).
% 7.67/1.35  fof(f64,plain,(
% 7.67/1.35    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 7.67/1.35    inference(definition_unfolding,[],[f48,f57,f57])).
% 7.67/1.35  fof(f48,plain,(
% 7.67/1.35    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 7.67/1.35    inference(cnf_transformation,[],[f17])).
% 7.67/1.35  fof(f17,axiom,(
% 7.67/1.35    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 7.67/1.35    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 7.67/1.37  fof(f155,plain,(
% 7.67/1.37    ( ! [X2,X1] : (r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X1)))) )),
% 7.67/1.37    inference(superposition,[],[f60,f61])).
% 7.67/1.37  fof(f34,plain,(
% 7.67/1.37    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 7.67/1.37    inference(cnf_transformation,[],[f22])).
% 7.67/1.37  fof(f22,plain,(
% 7.67/1.37    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 7.67/1.37    inference(flattening,[],[f21])).
% 7.67/1.37  fof(f21,plain,(
% 7.67/1.37    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 7.67/1.37    inference(ennf_transformation,[],[f19])).
% 7.67/1.37  fof(f19,negated_conjecture,(
% 7.67/1.37    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 7.67/1.37    inference(negated_conjecture,[],[f18])).
% 7.67/1.37  fof(f18,conjecture,(
% 7.67/1.37    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 7.67/1.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 7.67/1.37  fof(f8693,plain,(
% 7.67/1.37    spl6_21),
% 7.67/1.37    inference(avatar_contradiction_clause,[],[f8632])).
% 7.67/1.37  fof(f8632,plain,(
% 7.67/1.37    $false | spl6_21),
% 7.67/1.37    inference(unit_resulting_resolution,[],[f4492,f585,f33,f8455])).
% 7.67/1.37  fof(f33,plain,(
% 7.67/1.37    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 7.67/1.37    inference(cnf_transformation,[],[f22])).
% 7.67/1.37  fof(f585,plain,(
% 7.67/1.37    ( ! [X6,X4,X5] : (r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(k3_tarski(k1_enumset1(X4,X4,X6)),X5))) )),
% 7.67/1.37    inference(superposition,[],[f60,f64])).
% 7.67/1.37  fof(f4492,plain,(
% 7.67/1.37    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) | spl6_21),
% 7.67/1.37    inference(avatar_component_clause,[],[f4490])).
% 7.67/1.37  fof(f4490,plain,(
% 7.67/1.37    spl6_21 <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3))),
% 7.67/1.37    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 7.67/1.37  fof(f4497,plain,(
% 7.67/1.37    ~spl6_21 | ~spl6_22),
% 7.67/1.37    inference(avatar_split_clause,[],[f4453,f4494,f4490])).
% 7.67/1.37  fof(f4453,plain,(
% 7.67/1.37    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5)) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3))),
% 7.67/1.37    inference(resolution,[],[f512,f58])).
% 7.67/1.37  fof(f58,plain,(
% 7.67/1.37    ~r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 7.67/1.37    inference(definition_unfolding,[],[f35,f57,f57,f57])).
% 7.67/1.37  fof(f35,plain,(
% 7.67/1.37    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 7.67/1.37    inference(cnf_transformation,[],[f22])).
% 7.67/1.37  fof(f512,plain,(
% 7.67/1.37    ( ! [X21,X19,X22,X20,X18] : (r1_tarski(k3_tarski(k1_enumset1(X21,X21,X22)),k2_zfmisc_1(X18,k3_tarski(k1_enumset1(X19,X19,X20)))) | ~r1_tarski(X22,k2_zfmisc_1(X18,X20)) | ~r1_tarski(X21,k2_zfmisc_1(X18,X19))) )),
% 7.67/1.37    inference(superposition,[],[f67,f63])).
% 7.67/1.37  fof(f63,plain,(
% 7.67/1.37    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 7.67/1.37    inference(definition_unfolding,[],[f49,f57,f57])).
% 7.67/1.37  fof(f49,plain,(
% 7.67/1.37    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 7.67/1.37    inference(cnf_transformation,[],[f17])).
% 7.67/1.37  fof(f67,plain,(
% 7.67/1.37    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 7.67/1.37    inference(definition_unfolding,[],[f56,f57,f57])).
% 7.67/1.37  fof(f56,plain,(
% 7.67/1.37    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))) )),
% 7.67/1.37    inference(cnf_transformation,[],[f32])).
% 7.67/1.37  fof(f32,plain,(
% 7.67/1.37    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 7.67/1.37    inference(flattening,[],[f31])).
% 7.67/1.37  fof(f31,plain,(
% 7.67/1.37    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 7.67/1.37    inference(ennf_transformation,[],[f6])).
% 7.67/1.37  fof(f6,axiom,(
% 7.67/1.37    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 7.67/1.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
% 7.67/1.37  % SZS output end Proof for theBenchmark
% 7.67/1.37  % (10817)------------------------------
% 7.67/1.37  % (10817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.67/1.37  % (10817)Termination reason: Refutation
% 7.67/1.37  
% 7.67/1.37  % (10817)Memory used [KB]: 12792
% 7.67/1.37  % (10817)Time elapsed: 0.924 s
% 7.67/1.37  % (10817)------------------------------
% 7.67/1.37  % (10817)------------------------------
% 7.67/1.37  % (10795)Success in time 0.999 s
%------------------------------------------------------------------------------
