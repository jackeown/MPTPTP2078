%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:41 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 340 expanded)
%              Number of leaves         :   17 ( 115 expanded)
%              Depth                    :   14
%              Number of atoms          :  101 ( 383 expanded)
%              Number of equality atoms :   65 ( 335 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(subsumption_resolution,[],[f238,f110])).

fof(f110,plain,(
    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f49,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f49,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f26,f47,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f46])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f46])).

% (27481)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f238,plain,(
    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f237,f50])).

fof(f50,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f237,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f235,f135])).

fof(f135,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f134,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f134,plain,(
    ! [X5] : k3_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f133,f97])).

fof(f97,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(backward_demodulation,[],[f77,f95])).

fof(f95,plain,(
    ! [X4] : k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = X4 ),
    inference(forward_demodulation,[],[f89,f70])).

fof(f70,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f50,f51])).

fof(f89,plain,(
    ! [X4] : k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X4)) ),
    inference(superposition,[],[f54,f70])).

fof(f54,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f36,f47,f33,f47])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f77,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) = X3 ),
    inference(superposition,[],[f53,f70])).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f47,f33])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f133,plain,(
    ! [X5] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f128,f60])).

fof(f60,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f37,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f128,plain,(
    ! [X5] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k5_xboole_0(X5,k3_xboole_0(X5,X5)) ),
    inference(superposition,[],[f52,f70])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f34,f33,f33,f47])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f235,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f54,f233])).

fof(f233,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f66,f25])).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3) ) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (803831809)
% 0.13/0.36  ipcrm: permission denied for id (803864578)
% 0.13/0.36  ipcrm: permission denied for id (803930116)
% 0.13/0.36  ipcrm: permission denied for id (803995654)
% 0.13/0.37  ipcrm: permission denied for id (804028425)
% 0.13/0.37  ipcrm: permission denied for id (804061194)
% 0.13/0.37  ipcrm: permission denied for id (806420492)
% 0.13/0.37  ipcrm: permission denied for id (804159501)
% 0.13/0.37  ipcrm: permission denied for id (806453262)
% 0.13/0.37  ipcrm: permission denied for id (806486031)
% 0.13/0.38  ipcrm: permission denied for id (804225041)
% 0.13/0.38  ipcrm: permission denied for id (806551570)
% 0.13/0.38  ipcrm: permission denied for id (804257811)
% 0.13/0.38  ipcrm: permission denied for id (806617109)
% 0.13/0.38  ipcrm: permission denied for id (806649878)
% 0.13/0.38  ipcrm: permission denied for id (804323351)
% 0.13/0.39  ipcrm: permission denied for id (806682648)
% 0.13/0.39  ipcrm: permission denied for id (806715417)
% 0.13/0.39  ipcrm: permission denied for id (806748186)
% 0.13/0.39  ipcrm: permission denied for id (804421659)
% 0.13/0.39  ipcrm: permission denied for id (804454428)
% 0.13/0.39  ipcrm: permission denied for id (804487197)
% 0.13/0.39  ipcrm: permission denied for id (804519967)
% 0.13/0.39  ipcrm: permission denied for id (804552736)
% 0.13/0.40  ipcrm: permission denied for id (806944805)
% 0.20/0.41  ipcrm: permission denied for id (807141419)
% 0.20/0.41  ipcrm: permission denied for id (804618286)
% 0.20/0.41  ipcrm: permission denied for id (807239727)
% 0.20/0.41  ipcrm: permission denied for id (804651056)
% 0.20/0.42  ipcrm: permission denied for id (804683826)
% 0.20/0.42  ipcrm: permission denied for id (807305267)
% 0.20/0.42  ipcrm: permission denied for id (807338036)
% 0.20/0.42  ipcrm: permission denied for id (804847671)
% 0.20/0.42  ipcrm: permission denied for id (807436344)
% 0.20/0.42  ipcrm: permission denied for id (807469113)
% 0.20/0.43  ipcrm: permission denied for id (807534651)
% 0.20/0.43  ipcrm: permission denied for id (807567420)
% 0.20/0.43  ipcrm: permission denied for id (804945981)
% 0.20/0.43  ipcrm: permission denied for id (807600190)
% 0.20/0.43  ipcrm: permission denied for id (804978751)
% 0.20/0.43  ipcrm: permission denied for id (807632960)
% 0.20/0.44  ipcrm: permission denied for id (807764036)
% 0.20/0.44  ipcrm: permission denied for id (805109829)
% 0.20/0.44  ipcrm: permission denied for id (807796806)
% 0.20/0.44  ipcrm: permission denied for id (807829575)
% 0.20/0.44  ipcrm: permission denied for id (807862344)
% 0.20/0.44  ipcrm: permission denied for id (805240905)
% 0.20/0.45  ipcrm: permission denied for id (808058959)
% 0.20/0.45  ipcrm: permission denied for id (805404753)
% 0.20/0.45  ipcrm: permission denied for id (808124498)
% 0.20/0.45  ipcrm: permission denied for id (808157267)
% 0.20/0.45  ipcrm: permission denied for id (805437524)
% 0.20/0.46  ipcrm: permission denied for id (808190037)
% 0.20/0.46  ipcrm: permission denied for id (808222806)
% 0.20/0.46  ipcrm: permission denied for id (808288344)
% 0.20/0.46  ipcrm: permission denied for id (808419419)
% 0.20/0.46  ipcrm: permission denied for id (808452188)
% 0.20/0.47  ipcrm: permission denied for id (808484957)
% 0.20/0.47  ipcrm: permission denied for id (808517726)
% 0.20/0.47  ipcrm: permission denied for id (808550495)
% 0.20/0.47  ipcrm: permission denied for id (805634145)
% 0.20/0.47  ipcrm: permission denied for id (808616034)
% 0.20/0.48  ipcrm: permission denied for id (805732454)
% 0.20/0.48  ipcrm: permission denied for id (808845417)
% 0.20/0.48  ipcrm: permission denied for id (808910955)
% 0.20/0.48  ipcrm: permission denied for id (805830764)
% 0.20/0.48  ipcrm: permission denied for id (805863533)
% 0.20/0.49  ipcrm: permission denied for id (808943726)
% 0.20/0.49  ipcrm: permission denied for id (805896303)
% 0.20/0.49  ipcrm: permission denied for id (805929072)
% 0.20/0.49  ipcrm: permission denied for id (808976497)
% 0.20/0.49  ipcrm: permission denied for id (809074803)
% 0.20/0.49  ipcrm: permission denied for id (805994612)
% 0.20/0.49  ipcrm: permission denied for id (806027381)
% 0.20/0.50  ipcrm: permission denied for id (809107574)
% 0.20/0.50  ipcrm: permission denied for id (806092919)
% 0.20/0.50  ipcrm: permission denied for id (806125688)
% 0.20/0.50  ipcrm: permission denied for id (809173114)
% 0.20/0.51  ipcrm: permission denied for id (806191231)
% 0.85/0.62  % (27469)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.85/0.62  % (27469)Refutation not found, incomplete strategy% (27469)------------------------------
% 0.85/0.62  % (27469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.85/0.62  % (27469)Termination reason: Refutation not found, incomplete strategy
% 0.85/0.62  
% 0.85/0.62  % (27469)Memory used [KB]: 10618
% 0.85/0.62  % (27469)Time elapsed: 0.054 s
% 0.85/0.62  % (27469)------------------------------
% 0.85/0.62  % (27469)------------------------------
% 0.85/0.62  % (27487)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.85/0.62  % (27487)Refutation not found, incomplete strategy% (27487)------------------------------
% 0.85/0.62  % (27487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.85/0.62  % (27487)Termination reason: Refutation not found, incomplete strategy
% 0.85/0.62  
% 0.85/0.62  % (27487)Memory used [KB]: 10618
% 0.85/0.62  % (27487)Time elapsed: 0.057 s
% 0.85/0.62  % (27487)------------------------------
% 0.85/0.62  % (27487)------------------------------
% 1.03/0.63  % (27461)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.03/0.64  % (27470)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.22/0.65  % (27478)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.22/0.65  % (27460)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.65  % (27460)Refutation not found, incomplete strategy% (27460)------------------------------
% 1.22/0.65  % (27460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.65  % (27460)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.65  
% 1.22/0.65  % (27460)Memory used [KB]: 1663
% 1.22/0.65  % (27460)Time elapsed: 0.091 s
% 1.22/0.65  % (27460)------------------------------
% 1.22/0.65  % (27460)------------------------------
% 1.22/0.65  % (27459)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.66  % (27484)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.22/0.67  % (27467)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.22/0.67  % (27470)Refutation not found, incomplete strategy% (27470)------------------------------
% 1.22/0.67  % (27470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.67  % (27470)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.67  
% 1.22/0.67  % (27470)Memory used [KB]: 6268
% 1.22/0.67  % (27470)Time elapsed: 0.105 s
% 1.22/0.67  % (27470)------------------------------
% 1.22/0.67  % (27470)------------------------------
% 1.22/0.67  % (27468)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.22/0.67  % (27463)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.68  % (27476)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.22/0.68  % (27465)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.68  % (27476)Refutation not found, incomplete strategy% (27476)------------------------------
% 1.22/0.68  % (27476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.68  % (27476)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.68  
% 1.22/0.68  % (27476)Memory used [KB]: 1791
% 1.22/0.68  % (27476)Time elapsed: 0.126 s
% 1.22/0.68  % (27476)------------------------------
% 1.22/0.68  % (27476)------------------------------
% 1.22/0.68  % (27474)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.68  % (27482)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.22/0.68  % (27464)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.68  % (27480)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.22/0.68  % (27486)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.22/0.68  % (27486)Refutation not found, incomplete strategy% (27486)------------------------------
% 1.22/0.68  % (27486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.68  % (27486)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.68  
% 1.22/0.68  % (27486)Memory used [KB]: 6140
% 1.22/0.68  % (27486)Time elapsed: 0.139 s
% 1.22/0.68  % (27486)------------------------------
% 1.22/0.68  % (27486)------------------------------
% 1.22/0.69  % (27485)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.22/0.69  % (27485)Refutation not found, incomplete strategy% (27485)------------------------------
% 1.22/0.69  % (27485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (27485)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.69  
% 1.22/0.69  % (27485)Memory used [KB]: 6268
% 1.22/0.69  % (27485)Time elapsed: 0.135 s
% 1.22/0.69  % (27485)------------------------------
% 1.22/0.69  % (27485)------------------------------
% 1.22/0.69  % (27462)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.22/0.69  % (27473)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.22/0.69  % (27475)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.22/0.69  % (27473)Refutation not found, incomplete strategy% (27473)------------------------------
% 1.22/0.69  % (27473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (27473)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.69  
% 1.22/0.69  % (27473)Memory used [KB]: 1663
% 1.22/0.69  % (27473)Time elapsed: 0.107 s
% 1.22/0.69  % (27473)------------------------------
% 1.22/0.69  % (27473)------------------------------
% 1.22/0.69  % (27471)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.69  % (27488)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.22/0.69  % (27475)Refutation not found, incomplete strategy% (27475)------------------------------
% 1.22/0.69  % (27475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (27475)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.69  
% 1.22/0.69  % (27475)Memory used [KB]: 10618
% 1.22/0.69  % (27475)Time elapsed: 0.129 s
% 1.22/0.69  % (27475)------------------------------
% 1.22/0.69  % (27475)------------------------------
% 1.22/0.69  % (27488)Refutation not found, incomplete strategy% (27488)------------------------------
% 1.22/0.69  % (27488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (27488)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.69  
% 1.22/0.69  % (27488)Memory used [KB]: 1663
% 1.22/0.69  % (27488)Time elapsed: 0.134 s
% 1.22/0.69  % (27488)------------------------------
% 1.22/0.69  % (27488)------------------------------
% 1.22/0.69  % (27483)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.22/0.69  % (27471)Refutation not found, incomplete strategy% (27471)------------------------------
% 1.22/0.69  % (27471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (27471)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.69  
% 1.22/0.69  % (27471)Memory used [KB]: 10618
% 1.22/0.69  % (27471)Time elapsed: 0.131 s
% 1.22/0.69  % (27471)------------------------------
% 1.22/0.69  % (27471)------------------------------
% 1.22/0.69  % (27483)Refutation not found, incomplete strategy% (27483)------------------------------
% 1.22/0.69  % (27483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (27483)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.69  
% 1.22/0.69  % (27483)Memory used [KB]: 10618
% 1.22/0.69  % (27483)Time elapsed: 0.134 s
% 1.22/0.69  % (27483)------------------------------
% 1.22/0.69  % (27483)------------------------------
% 1.22/0.69  % (27466)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.22/0.69  % (27472)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.22/0.70  % (27477)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.22/0.70  % (27477)Refutation not found, incomplete strategy% (27477)------------------------------
% 1.22/0.70  % (27477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.70  % (27477)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.70  
% 1.22/0.70  % (27477)Memory used [KB]: 1663
% 1.22/0.70  % (27477)Time elapsed: 0.123 s
% 1.22/0.70  % (27477)------------------------------
% 1.22/0.70  % (27477)------------------------------
% 1.22/0.70  % (27479)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.70  % (27465)Refutation found. Thanks to Tanya!
% 1.22/0.70  % SZS status Theorem for theBenchmark
% 1.22/0.70  % SZS output start Proof for theBenchmark
% 1.22/0.70  fof(f239,plain,(
% 1.22/0.70    $false),
% 1.22/0.70    inference(subsumption_resolution,[],[f238,f110])).
% 1.22/0.70  fof(f110,plain,(
% 1.22/0.70    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.22/0.70    inference(forward_demodulation,[],[f49,f51])).
% 1.22/0.70  fof(f51,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.22/0.70    inference(definition_unfolding,[],[f30,f46,f46])).
% 1.22/0.70  fof(f46,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.22/0.70    inference(definition_unfolding,[],[f31,f45])).
% 1.22/0.70  fof(f45,plain,(
% 1.22/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.22/0.70    inference(definition_unfolding,[],[f43,f44])).
% 1.22/0.70  fof(f44,plain,(
% 1.22/0.70    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.22/0.70    inference(cnf_transformation,[],[f13])).
% 1.22/0.70  fof(f13,axiom,(
% 1.22/0.70    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.22/0.70  fof(f43,plain,(
% 1.22/0.70    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.22/0.70    inference(cnf_transformation,[],[f12])).
% 1.22/0.70  fof(f12,axiom,(
% 1.22/0.70    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.22/0.70  fof(f31,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.22/0.70    inference(cnf_transformation,[],[f11])).
% 1.22/0.70  fof(f11,axiom,(
% 1.22/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.22/0.70  fof(f30,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.22/0.70    inference(cnf_transformation,[],[f9])).
% 1.22/0.70  fof(f9,axiom,(
% 1.22/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.22/0.70  fof(f49,plain,(
% 1.22/0.70    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.22/0.70    inference(definition_unfolding,[],[f26,f47,f48])).
% 1.22/0.70  fof(f48,plain,(
% 1.22/0.70    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.22/0.70    inference(definition_unfolding,[],[f29,f46])).
% 1.22/0.70  fof(f29,plain,(
% 1.22/0.70    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.22/0.70    inference(cnf_transformation,[],[f10])).
% 1.22/0.70  fof(f10,axiom,(
% 1.22/0.70    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.22/0.70  fof(f47,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.22/0.70    inference(definition_unfolding,[],[f32,f46])).
% 1.22/0.70  % (27481)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.22/0.70  fof(f32,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.22/0.70    inference(cnf_transformation,[],[f15])).
% 1.22/0.70  fof(f15,axiom,(
% 1.22/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.22/0.70  fof(f26,plain,(
% 1.22/0.70    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.22/0.70    inference(cnf_transformation,[],[f21])).
% 1.22/0.70  fof(f21,plain,(
% 1.22/0.70    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.22/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 1.22/0.70  fof(f20,plain,(
% 1.22/0.70    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.22/0.70    introduced(choice_axiom,[])).
% 1.22/0.70  fof(f18,plain,(
% 1.22/0.70    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.22/0.70    inference(ennf_transformation,[],[f17])).
% 1.22/0.70  fof(f17,negated_conjecture,(
% 1.22/0.70    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.22/0.70    inference(negated_conjecture,[],[f16])).
% 1.22/0.70  fof(f16,conjecture,(
% 1.22/0.70    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.22/0.70  fof(f238,plain,(
% 1.22/0.70    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.22/0.70    inference(forward_demodulation,[],[f237,f50])).
% 1.22/0.70  fof(f50,plain,(
% 1.22/0.70    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.22/0.70    inference(definition_unfolding,[],[f28,f47])).
% 1.22/0.70  fof(f28,plain,(
% 1.22/0.70    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.22/0.70    inference(cnf_transformation,[],[f3])).
% 1.22/0.70  fof(f3,axiom,(
% 1.22/0.70    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.22/0.70  fof(f237,plain,(
% 1.22/0.70    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))),
% 1.22/0.70    inference(forward_demodulation,[],[f235,f135])).
% 1.22/0.70  fof(f135,plain,(
% 1.22/0.70    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 1.22/0.70    inference(forward_demodulation,[],[f134,f59])).
% 1.22/0.70  fof(f59,plain,(
% 1.22/0.70    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.22/0.70    inference(resolution,[],[f37,f27])).
% 1.22/0.70  fof(f27,plain,(
% 1.22/0.70    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.22/0.70    inference(cnf_transformation,[],[f5])).
% 1.22/0.70  fof(f5,axiom,(
% 1.22/0.70    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.22/0.70  fof(f37,plain,(
% 1.22/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.22/0.70    inference(cnf_transformation,[],[f19])).
% 1.22/0.70  fof(f19,plain,(
% 1.22/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.22/0.70    inference(ennf_transformation,[],[f4])).
% 1.22/0.70  fof(f4,axiom,(
% 1.22/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.22/0.70  fof(f134,plain,(
% 1.22/0.70    ( ! [X5] : (k3_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5)) )),
% 1.22/0.70    inference(forward_demodulation,[],[f133,f97])).
% 1.22/0.70  fof(f97,plain,(
% 1.22/0.70    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = X3) )),
% 1.22/0.70    inference(backward_demodulation,[],[f77,f95])).
% 1.22/0.70  fof(f95,plain,(
% 1.22/0.70    ( ! [X4] : (k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = X4) )),
% 1.22/0.70    inference(forward_demodulation,[],[f89,f70])).
% 1.22/0.70  fof(f70,plain,(
% 1.22/0.70    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.22/0.70    inference(superposition,[],[f50,f51])).
% 1.22/0.70  fof(f89,plain,(
% 1.22/0.70    ( ! [X4] : (k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X4))) )),
% 1.22/0.70    inference(superposition,[],[f54,f70])).
% 1.22/0.70  fof(f54,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.22/0.70    inference(definition_unfolding,[],[f36,f47,f33,f47])).
% 1.22/0.70  fof(f33,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.22/0.70    inference(cnf_transformation,[],[f2])).
% 1.22/0.70  fof(f2,axiom,(
% 1.22/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.22/0.70  fof(f36,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.22/0.70    inference(cnf_transformation,[],[f6])).
% 1.22/0.70  fof(f6,axiom,(
% 1.22/0.70    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.22/0.70  fof(f77,plain,(
% 1.22/0.70    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))) = X3) )),
% 1.22/0.70    inference(superposition,[],[f53,f70])).
% 1.22/0.70  fof(f53,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.22/0.70    inference(definition_unfolding,[],[f35,f47,f33])).
% 1.22/0.70  fof(f35,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.22/0.70    inference(cnf_transformation,[],[f8])).
% 1.22/0.70  fof(f8,axiom,(
% 1.22/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.22/0.70  fof(f133,plain,(
% 1.22/0.70    ( ! [X5] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k5_xboole_0(X5,X5)) )),
% 1.22/0.70    inference(forward_demodulation,[],[f128,f60])).
% 1.22/0.70  fof(f60,plain,(
% 1.22/0.70    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.22/0.70    inference(resolution,[],[f37,f57])).
% 1.22/0.70  fof(f57,plain,(
% 1.22/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.22/0.70    inference(equality_resolution,[],[f39])).
% 1.22/0.70  fof(f39,plain,(
% 1.22/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.22/0.70    inference(cnf_transformation,[],[f23])).
% 1.22/0.70  fof(f23,plain,(
% 1.22/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.22/0.70    inference(flattening,[],[f22])).
% 1.22/0.70  fof(f22,plain,(
% 1.22/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.22/0.70    inference(nnf_transformation,[],[f1])).
% 1.22/0.70  fof(f1,axiom,(
% 1.22/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.22/0.70  fof(f128,plain,(
% 1.22/0.70    ( ! [X5] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) = k5_xboole_0(X5,k3_xboole_0(X5,X5))) )),
% 1.22/0.70    inference(superposition,[],[f52,f70])).
% 1.22/0.70  fof(f52,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.22/0.70    inference(definition_unfolding,[],[f34,f33,f33,f47])).
% 1.22/0.70  fof(f34,plain,(
% 1.22/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.22/0.70    inference(cnf_transformation,[],[f7])).
% 1.22/0.70  fof(f7,axiom,(
% 1.22/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.22/0.70  fof(f235,plain,(
% 1.22/0.70    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 1.22/0.70    inference(superposition,[],[f54,f233])).
% 1.22/0.70  fof(f233,plain,(
% 1.22/0.70    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.22/0.70    inference(resolution,[],[f66,f25])).
% 1.22/0.70  fof(f25,plain,(
% 1.22/0.70    r2_hidden(sK0,sK1)),
% 1.22/0.70    inference(cnf_transformation,[],[f21])).
% 1.22/0.70  fof(f66,plain,(
% 1.22/0.70    ( ! [X2,X3] : (~r2_hidden(X2,X3) | k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X3)) )),
% 1.22/0.70    inference(resolution,[],[f55,f37])).
% 1.22/0.70  fof(f55,plain,(
% 1.22/0.70    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.22/0.70    inference(definition_unfolding,[],[f42,f48])).
% 1.22/0.70  fof(f42,plain,(
% 1.22/0.70    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.22/0.70    inference(cnf_transformation,[],[f24])).
% 1.22/0.70  fof(f24,plain,(
% 1.22/0.70    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.22/0.70    inference(nnf_transformation,[],[f14])).
% 1.22/0.70  fof(f14,axiom,(
% 1.22/0.70    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.22/0.70  % SZS output end Proof for theBenchmark
% 1.22/0.70  % (27465)------------------------------
% 1.22/0.70  % (27465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.70  % (27465)Termination reason: Refutation
% 1.22/0.70  
% 1.22/0.70  % (27465)Memory used [KB]: 10746
% 1.22/0.70  % (27465)Time elapsed: 0.107 s
% 1.22/0.70  % (27465)------------------------------
% 1.22/0.70  % (27465)------------------------------
% 1.22/0.70  % (27323)Success in time 0.342 s
%------------------------------------------------------------------------------
