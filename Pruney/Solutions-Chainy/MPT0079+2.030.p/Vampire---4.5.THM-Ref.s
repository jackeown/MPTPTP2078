%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:55 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 508 expanded)
%              Number of leaves         :   13 ( 158 expanded)
%              Depth                    :   23
%              Number of atoms          :  115 ( 852 expanded)
%              Number of equality atoms :   93 ( 619 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2345,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2344])).

fof(f2344,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f28,f2243])).

fof(f2243,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f462,f2242])).

fof(f2242,plain,(
    sK1 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f2241,f2172])).

fof(f2172,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f1751,f2055])).

fof(f2055,plain,(
    sK0 = sK3 ),
    inference(forward_demodulation,[],[f2043,f1409])).

fof(f1409,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1387,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1387,plain,(
    k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f35,f1361])).

fof(f1361,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f908,f86])).

fof(f86,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f85,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f46,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f85,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f36,f84])).

fof(f84,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f83,f25])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f83,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f82,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f82,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f81,f35])).

fof(f81,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f35,f69])).

fof(f69,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f36,f25])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f908,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f500,f32])).

fof(f500,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f44,f474])).

fof(f474,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f439,f31])).

fof(f439,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f47,f117])).

fof(f117,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f39,f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2043,plain,(
    sK3 = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f2036,f32])).

fof(f2036,plain,(
    sK3 = k2_xboole_0(sK3,sK0) ),
    inference(forward_demodulation,[],[f2027,f30])).

fof(f2027,plain,(
    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f35,f1926])).

fof(f1926,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1907,f306])).

fof(f306,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f288,f77])).

fof(f77,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8) ),
    inference(forward_demodulation,[],[f73,f52])).

fof(f73,plain,(
    ! [X8] : k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X8,X8) ),
    inference(superposition,[],[f36,f53])).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f32,f30])).

fof(f288,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f44,f52])).

fof(f1907,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f1773,f25])).

fof(f1773,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f44,f1733])).

fof(f1733,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f1507,f462])).

fof(f1507,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(backward_demodulation,[],[f798,f1481])).

fof(f1481,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f848,f32])).

fof(f848,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5 ),
    inference(forward_demodulation,[],[f847,f31])).

fof(f847,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f755,f52])).

fof(f755,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X6,X6)) ),
    inference(superposition,[],[f51,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f45,f33])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f798,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f797,f32])).

fof(f797,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f729,f31])).

fof(f729,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f51,f52])).

fof(f1751,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f1507,f474])).

fof(f2241,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f2234,f70])).

fof(f70,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f36,f32])).

fof(f2234,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f36,f2056])).

fof(f2056,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f25,f2055])).

fof(f462,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f438,f31])).

fof(f438,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f47,f116])).

fof(f116,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f50,f26])).

fof(f26,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:48:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (23143)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (23166)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (23142)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (23150)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (23151)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (23160)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (23141)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (23152)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (23157)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (23147)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (23138)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (23140)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (23159)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (23167)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (23154)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (23162)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (23139)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.55  % (23156)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (23144)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (23165)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (23153)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (23153)Refutation not found, incomplete strategy% (23153)------------------------------
% 0.20/0.55  % (23153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (23153)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (23153)Memory used [KB]: 6140
% 0.20/0.55  % (23153)Time elapsed: 0.002 s
% 0.20/0.55  % (23153)------------------------------
% 0.20/0.55  % (23153)------------------------------
% 0.20/0.55  % (23163)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (23164)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (23158)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (23145)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (23161)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (23149)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (23155)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (23155)Refutation not found, incomplete strategy% (23155)------------------------------
% 0.20/0.56  % (23155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (23155)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (23155)Memory used [KB]: 10618
% 0.20/0.56  % (23155)Time elapsed: 0.148 s
% 0.20/0.56  % (23155)------------------------------
% 0.20/0.56  % (23155)------------------------------
% 0.20/0.56  % (23148)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (23146)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.04/0.64  % (23150)Refutation found. Thanks to Tanya!
% 2.04/0.64  % SZS status Theorem for theBenchmark
% 2.04/0.65  % SZS output start Proof for theBenchmark
% 2.04/0.65  fof(f2345,plain,(
% 2.04/0.65    $false),
% 2.04/0.65    inference(trivial_inequality_removal,[],[f2344])).
% 2.04/0.65  fof(f2344,plain,(
% 2.04/0.65    sK1 != sK1),
% 2.04/0.65    inference(superposition,[],[f28,f2243])).
% 2.04/0.65  fof(f2243,plain,(
% 2.04/0.65    sK1 = sK2),
% 2.04/0.65    inference(backward_demodulation,[],[f462,f2242])).
% 2.04/0.65  fof(f2242,plain,(
% 2.04/0.65    sK1 = k4_xboole_0(sK2,sK0)),
% 2.04/0.65    inference(forward_demodulation,[],[f2241,f2172])).
% 2.04/0.65  fof(f2172,plain,(
% 2.04/0.65    sK1 = k4_xboole_0(sK1,sK0)),
% 2.04/0.65    inference(backward_demodulation,[],[f1751,f2055])).
% 2.04/0.65  fof(f2055,plain,(
% 2.04/0.65    sK0 = sK3),
% 2.04/0.65    inference(forward_demodulation,[],[f2043,f1409])).
% 2.04/0.65  fof(f1409,plain,(
% 2.04/0.65    sK0 = k2_xboole_0(sK0,sK3)),
% 2.04/0.65    inference(forward_demodulation,[],[f1387,f30])).
% 2.04/0.65  fof(f30,plain,(
% 2.04/0.65    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.04/0.65    inference(cnf_transformation,[],[f5])).
% 2.04/0.65  fof(f5,axiom,(
% 2.04/0.65    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.04/0.65  fof(f1387,plain,(
% 2.04/0.65    k2_xboole_0(sK0,sK3) = k2_xboole_0(sK0,k1_xboole_0)),
% 2.04/0.65    inference(superposition,[],[f35,f1361])).
% 2.04/0.65  fof(f1361,plain,(
% 2.04/0.65    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 2.04/0.65    inference(superposition,[],[f908,f86])).
% 2.04/0.65  fof(f86,plain,(
% 2.04/0.65    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.04/0.65    inference(forward_demodulation,[],[f85,f52])).
% 2.04/0.65  fof(f52,plain,(
% 2.04/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.04/0.65    inference(backward_demodulation,[],[f46,f31])).
% 2.04/0.65  fof(f31,plain,(
% 2.04/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.04/0.65    inference(cnf_transformation,[],[f8])).
% 2.04/0.65  fof(f8,axiom,(
% 2.04/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.04/0.65  fof(f46,plain,(
% 2.04/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.04/0.65    inference(definition_unfolding,[],[f29,f33])).
% 2.04/0.65  fof(f33,plain,(
% 2.04/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.04/0.65    inference(cnf_transformation,[],[f12])).
% 2.04/0.65  fof(f12,axiom,(
% 2.04/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.04/0.65  fof(f29,plain,(
% 2.04/0.65    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f6])).
% 2.04/0.65  fof(f6,axiom,(
% 2.04/0.65    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.04/0.65  fof(f85,plain,(
% 2.04/0.65    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.04/0.65    inference(superposition,[],[f36,f84])).
% 2.04/0.65  fof(f84,plain,(
% 2.04/0.65    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.04/0.65    inference(forward_demodulation,[],[f83,f25])).
% 2.04/0.65  fof(f25,plain,(
% 2.04/0.65    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.04/0.65    inference(cnf_transformation,[],[f22])).
% 2.04/0.65  fof(f22,plain,(
% 2.04/0.65    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.04/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f21])).
% 2.04/0.65  fof(f21,plain,(
% 2.04/0.65    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 2.04/0.65    introduced(choice_axiom,[])).
% 2.04/0.65  fof(f19,plain,(
% 2.04/0.65    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.04/0.65    inference(flattening,[],[f18])).
% 2.04/0.65  fof(f18,plain,(
% 2.04/0.65    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.04/0.65    inference(ennf_transformation,[],[f17])).
% 2.04/0.65  fof(f17,negated_conjecture,(
% 2.04/0.65    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.04/0.65    inference(negated_conjecture,[],[f16])).
% 2.04/0.65  fof(f16,conjecture,(
% 2.04/0.65    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.04/0.65  fof(f83,plain,(
% 2.04/0.65    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.04/0.65    inference(forward_demodulation,[],[f82,f32])).
% 2.04/0.65  fof(f32,plain,(
% 2.04/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f1])).
% 2.04/0.65  fof(f1,axiom,(
% 2.04/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.04/0.65  fof(f82,plain,(
% 2.04/0.65    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.04/0.65    inference(forward_demodulation,[],[f81,f35])).
% 2.04/0.65  fof(f81,plain,(
% 2.04/0.65    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 2.04/0.65    inference(superposition,[],[f35,f69])).
% 2.04/0.65  fof(f69,plain,(
% 2.04/0.65    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.04/0.65    inference(superposition,[],[f36,f25])).
% 2.04/0.65  fof(f36,plain,(
% 2.04/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f9])).
% 2.04/0.65  fof(f9,axiom,(
% 2.04/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.04/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.04/0.65  fof(f908,plain,(
% 2.04/0.65    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 2.04/0.65    inference(superposition,[],[f500,f32])).
% 2.04/0.65  fof(f500,plain,(
% 2.04/0.65    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 2.04/0.65    inference(superposition,[],[f44,f474])).
% 2.04/0.65  fof(f474,plain,(
% 2.04/0.65    sK3 = k4_xboole_0(sK3,sK1)),
% 2.04/0.65    inference(forward_demodulation,[],[f439,f31])).
% 2.04/0.65  fof(f439,plain,(
% 2.04/0.65    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 2.04/0.65    inference(superposition,[],[f47,f117])).
% 2.04/0.65  fof(f117,plain,(
% 2.04/0.65    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 2.04/0.65    inference(resolution,[],[f50,f27])).
% 2.04/0.65  fof(f27,plain,(
% 2.04/0.65    r1_xboole_0(sK3,sK1)),
% 2.04/0.65    inference(cnf_transformation,[],[f22])).
% 2.04/0.65  fof(f50,plain,(
% 2.04/0.65    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.04/0.65    inference(definition_unfolding,[],[f39,f33])).
% 2.04/0.65  fof(f39,plain,(
% 2.04/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.04/0.65    inference(cnf_transformation,[],[f23])).
% 2.04/0.65  fof(f23,plain,(
% 2.04/0.65    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.04/0.65    inference(nnf_transformation,[],[f2])).
% 2.04/0.66  fof(f2,axiom,(
% 2.04/0.66    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.04/0.66  fof(f47,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.04/0.66    inference(definition_unfolding,[],[f34,f33])).
% 2.04/0.66  fof(f34,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f11])).
% 2.04/0.66  fof(f11,axiom,(
% 2.04/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.04/0.66  fof(f44,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f10])).
% 2.04/0.66  fof(f10,axiom,(
% 2.04/0.66    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.04/0.66  fof(f35,plain,(
% 2.04/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f7])).
% 2.04/0.66  fof(f7,axiom,(
% 2.04/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.04/0.66  fof(f2043,plain,(
% 2.04/0.66    sK3 = k2_xboole_0(sK0,sK3)),
% 2.04/0.66    inference(superposition,[],[f2036,f32])).
% 2.04/0.66  fof(f2036,plain,(
% 2.04/0.66    sK3 = k2_xboole_0(sK3,sK0)),
% 2.04/0.66    inference(forward_demodulation,[],[f2027,f30])).
% 2.04/0.66  fof(f2027,plain,(
% 2.04/0.66    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0)),
% 2.04/0.66    inference(superposition,[],[f35,f1926])).
% 2.04/0.66  fof(f1926,plain,(
% 2.04/0.66    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 2.04/0.66    inference(forward_demodulation,[],[f1907,f306])).
% 2.04/0.66  fof(f306,plain,(
% 2.04/0.66    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.04/0.66    inference(forward_demodulation,[],[f288,f77])).
% 2.04/0.66  fof(f77,plain,(
% 2.04/0.66    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8)) )),
% 2.04/0.66    inference(forward_demodulation,[],[f73,f52])).
% 2.04/0.66  fof(f73,plain,(
% 2.04/0.66    ( ! [X8] : (k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X8,X8)) )),
% 2.04/0.66    inference(superposition,[],[f36,f53])).
% 2.04/0.66  fof(f53,plain,(
% 2.04/0.66    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.04/0.66    inference(superposition,[],[f32,f30])).
% 2.04/0.66  fof(f288,plain,(
% 2.04/0.66    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 2.04/0.66    inference(superposition,[],[f44,f52])).
% 2.04/0.66  fof(f1907,plain,(
% 2.04/0.66    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3)),
% 2.04/0.66    inference(superposition,[],[f1773,f25])).
% 2.04/0.66  fof(f1773,plain,(
% 2.04/0.66    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))) )),
% 2.04/0.66    inference(superposition,[],[f44,f1733])).
% 2.04/0.66  fof(f1733,plain,(
% 2.04/0.66    sK0 = k4_xboole_0(sK0,sK2)),
% 2.04/0.66    inference(superposition,[],[f1507,f462])).
% 2.04/0.66  fof(f1507,plain,(
% 2.04/0.66    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 2.04/0.66    inference(backward_demodulation,[],[f798,f1481])).
% 2.04/0.66  fof(f1481,plain,(
% 2.04/0.66    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 2.04/0.66    inference(superposition,[],[f848,f32])).
% 2.04/0.66  fof(f848,plain,(
% 2.04/0.66    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) )),
% 2.04/0.66    inference(forward_demodulation,[],[f847,f31])).
% 2.04/0.66  fof(f847,plain,(
% 2.04/0.66    ( ! [X6,X5] : (k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 2.04/0.66    inference(forward_demodulation,[],[f755,f52])).
% 2.04/0.66  fof(f755,plain,(
% 2.04/0.66    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(X5,k4_xboole_0(X6,X6))) )),
% 2.04/0.66    inference(superposition,[],[f51,f35])).
% 2.04/0.66  fof(f51,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.04/0.66    inference(definition_unfolding,[],[f45,f33])).
% 2.04/0.66  fof(f45,plain,(
% 2.04/0.66    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.04/0.66    inference(cnf_transformation,[],[f15])).
% 2.04/0.66  fof(f15,axiom,(
% 2.04/0.66    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.04/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 2.04/0.66  fof(f798,plain,(
% 2.04/0.66    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.04/0.66    inference(forward_demodulation,[],[f797,f32])).
% 2.04/0.66  fof(f797,plain,(
% 2.04/0.66    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 2.04/0.66    inference(forward_demodulation,[],[f729,f31])).
% 2.04/0.66  fof(f729,plain,(
% 2.04/0.66    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))) )),
% 2.04/0.66    inference(superposition,[],[f51,f52])).
% 2.04/0.66  fof(f1751,plain,(
% 2.04/0.66    sK1 = k4_xboole_0(sK1,sK3)),
% 2.04/0.66    inference(superposition,[],[f1507,f474])).
% 2.04/0.66  fof(f2241,plain,(
% 2.04/0.66    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0)),
% 2.04/0.66    inference(forward_demodulation,[],[f2234,f70])).
% 2.04/0.66  fof(f70,plain,(
% 2.04/0.66    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 2.04/0.66    inference(superposition,[],[f36,f32])).
% 2.04/0.66  fof(f2234,plain,(
% 2.04/0.66    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)),
% 2.04/0.66    inference(superposition,[],[f36,f2056])).
% 2.04/0.66  fof(f2056,plain,(
% 2.04/0.66    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)),
% 2.04/0.66    inference(backward_demodulation,[],[f25,f2055])).
% 2.04/0.66  fof(f462,plain,(
% 2.04/0.66    sK2 = k4_xboole_0(sK2,sK0)),
% 2.04/0.66    inference(forward_demodulation,[],[f438,f31])).
% 2.04/0.66  fof(f438,plain,(
% 2.04/0.66    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 2.04/0.66    inference(superposition,[],[f47,f116])).
% 2.04/0.66  fof(f116,plain,(
% 2.04/0.66    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.04/0.66    inference(resolution,[],[f50,f26])).
% 2.04/0.66  fof(f26,plain,(
% 2.04/0.66    r1_xboole_0(sK2,sK0)),
% 2.04/0.66    inference(cnf_transformation,[],[f22])).
% 2.04/0.66  fof(f28,plain,(
% 2.04/0.66    sK1 != sK2),
% 2.04/0.66    inference(cnf_transformation,[],[f22])).
% 2.04/0.66  % SZS output end Proof for theBenchmark
% 2.04/0.66  % (23150)------------------------------
% 2.04/0.66  % (23150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.66  % (23150)Termination reason: Refutation
% 2.04/0.66  
% 2.04/0.66  % (23150)Memory used [KB]: 7547
% 2.04/0.66  % (23150)Time elapsed: 0.215 s
% 2.04/0.66  % (23150)------------------------------
% 2.04/0.66  % (23150)------------------------------
% 2.04/0.66  % (23137)Success in time 0.294 s
%------------------------------------------------------------------------------
