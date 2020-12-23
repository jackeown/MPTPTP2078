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
% DateTime   : Thu Dec  3 12:52:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 179 expanded)
%              Number of leaves         :   15 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  140 ( 300 expanded)
%              Number of equality atoms :   68 ( 118 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1067,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1065])).

fof(f1065,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f44,f798])).

fof(f798,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f84,f797])).

fof(f797,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f796,f131])).

fof(f131,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(k3_xboole_0(X1,X2))) ),
    inference(resolution,[],[f96,f50])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f95,f84])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f94,f47])).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f60,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f796,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f784,f163])).

fof(f163,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X1,X0)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f131,f125])).

fof(f125,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f74,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f53,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f784,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k3_xboole_0(X2,X3)))) ),
    inference(resolution,[],[f143,f72])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f143,plain,(
    ! [X26,X24,X25] :
      ( ~ r1_tarski(k3_xboole_0(X24,X25),X26)
      | k8_relat_1(X24,k6_relat_1(X25)) = k8_relat_1(X24,k8_relat_1(X25,k6_relat_1(X26))) ) ),
    inference(backward_demodulation,[],[f119,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] : k7_relat_1(k8_relat_1(X0,k6_relat_1(X2)),X1) = k8_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f141,f84])).

fof(f141,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X2)),X1) ),
    inference(forward_demodulation,[],[f139,f105])).

fof(f105,plain,(
    ! [X10,X11,X9] : k5_relat_1(k6_relat_1(X9),k8_relat_1(X10,k6_relat_1(X11))) = k7_relat_1(k8_relat_1(X10,k6_relat_1(X11)),X9) ),
    inference(resolution,[],[f93,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f93,plain,(
    ! [X0,X1] : v1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f92,f84])).

fof(f92,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(resolution,[],[f78,f45])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f63,f45])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f139,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
    inference(resolution,[],[f100,f45])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(X1,k8_relat_1(X0,k6_relat_1(X2))) ) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

fof(f119,plain,(
    ! [X26,X24,X25] :
      ( k8_relat_1(X24,k6_relat_1(X25)) = k7_relat_1(k8_relat_1(X24,k6_relat_1(X25)),X26)
      | ~ r1_tarski(k3_xboole_0(X24,X25),X26) ) ),
    inference(forward_demodulation,[],[f118,f105])).

fof(f118,plain,(
    ! [X26,X24,X25] :
      ( ~ r1_tarski(k3_xboole_0(X24,X25),X26)
      | k8_relat_1(X24,k6_relat_1(X25)) = k5_relat_1(k6_relat_1(X26),k8_relat_1(X24,k6_relat_1(X25))) ) ),
    inference(forward_demodulation,[],[f110,f91])).

fof(f91,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f90,f88])).

fof(f88,plain,(
    ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f87,f84])).

fof(f87,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f56,f45])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f89,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(resolution,[],[f57,f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f110,plain,(
    ! [X26,X24,X25] :
      ( ~ r1_tarski(k1_relat_1(k8_relat_1(X24,k6_relat_1(X25))),X26)
      | k8_relat_1(X24,k6_relat_1(X25)) = k5_relat_1(k6_relat_1(X26),k8_relat_1(X24,k6_relat_1(X25))) ) ),
    inference(resolution,[],[f93,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f84,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f44,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f40])).

fof(f40,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (4644)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.49  % (4636)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.49  % (4644)Refutation not found, incomplete strategy% (4644)------------------------------
% 0.21/0.49  % (4644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4644)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (4644)Memory used [KB]: 6140
% 0.21/0.49  % (4644)Time elapsed: 0.087 s
% 0.21/0.49  % (4644)------------------------------
% 0.21/0.49  % (4644)------------------------------
% 0.21/0.50  % (4656)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (4655)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (4639)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (4634)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (4637)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (4634)Refutation not found, incomplete strategy% (4634)------------------------------
% 0.21/0.51  % (4634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4634)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4634)Memory used [KB]: 1663
% 0.21/0.51  % (4634)Time elapsed: 0.095 s
% 0.21/0.51  % (4634)------------------------------
% 0.21/0.51  % (4634)------------------------------
% 0.21/0.51  % (4660)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (4660)Refutation not found, incomplete strategy% (4660)------------------------------
% 0.21/0.51  % (4660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4660)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4660)Memory used [KB]: 6140
% 0.21/0.51  % (4660)Time elapsed: 0.109 s
% 0.21/0.51  % (4660)------------------------------
% 0.21/0.51  % (4660)------------------------------
% 0.21/0.52  % (4642)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (4633)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (4650)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (4635)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (4650)Refutation not found, incomplete strategy% (4650)------------------------------
% 0.21/0.53  % (4650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4650)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4650)Memory used [KB]: 1663
% 0.21/0.53  % (4650)Time elapsed: 0.127 s
% 0.21/0.53  % (4650)------------------------------
% 0.21/0.53  % (4650)------------------------------
% 0.21/0.53  % (4641)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (4661)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (4640)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (4659)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (4659)Refutation not found, incomplete strategy% (4659)------------------------------
% 0.21/0.54  % (4659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4659)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4659)Memory used [KB]: 6140
% 0.21/0.54  % (4659)Time elapsed: 0.128 s
% 0.21/0.54  % (4659)------------------------------
% 0.21/0.54  % (4659)------------------------------
% 0.21/0.54  % (4661)Refutation not found, incomplete strategy% (4661)------------------------------
% 0.21/0.54  % (4661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4661)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4661)Memory used [KB]: 10746
% 0.21/0.54  % (4661)Time elapsed: 0.129 s
% 0.21/0.54  % (4661)------------------------------
% 0.21/0.54  % (4661)------------------------------
% 0.21/0.54  % (4658)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (4654)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (4658)Refutation not found, incomplete strategy% (4658)------------------------------
% 0.21/0.54  % (4658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4658)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4658)Memory used [KB]: 6140
% 0.21/0.54  % (4658)Time elapsed: 0.138 s
% 0.21/0.54  % (4658)------------------------------
% 0.21/0.54  % (4658)------------------------------
% 0.21/0.54  % (4643)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (4645)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (4647)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (4643)Refutation not found, incomplete strategy% (4643)------------------------------
% 0.21/0.54  % (4643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4643)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4643)Memory used [KB]: 10618
% 0.21/0.54  % (4643)Time elapsed: 0.139 s
% 0.21/0.54  % (4643)------------------------------
% 0.21/0.54  % (4643)------------------------------
% 0.21/0.55  % (4645)Refutation not found, incomplete strategy% (4645)------------------------------
% 0.21/0.55  % (4645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4645)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4645)Memory used [KB]: 10618
% 0.21/0.55  % (4645)Time elapsed: 0.141 s
% 0.21/0.55  % (4645)------------------------------
% 0.21/0.55  % (4645)------------------------------
% 0.21/0.55  % (4647)Refutation not found, incomplete strategy% (4647)------------------------------
% 0.21/0.55  % (4647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4647)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4647)Memory used [KB]: 1663
% 0.21/0.55  % (4647)Time elapsed: 0.140 s
% 0.21/0.55  % (4647)------------------------------
% 0.21/0.55  % (4647)------------------------------
% 0.21/0.55  % (4648)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (4651)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (4651)Refutation not found, incomplete strategy% (4651)------------------------------
% 0.21/0.55  % (4651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4651)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4651)Memory used [KB]: 1663
% 0.21/0.55  % (4651)Time elapsed: 0.141 s
% 0.21/0.55  % (4651)------------------------------
% 0.21/0.55  % (4651)------------------------------
% 0.21/0.55  % (4649)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (4653)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (4649)Refutation not found, incomplete strategy% (4649)------------------------------
% 0.21/0.55  % (4649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4649)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4649)Memory used [KB]: 10618
% 0.21/0.55  % (4649)Time elapsed: 0.140 s
% 0.21/0.55  % (4649)------------------------------
% 0.21/0.55  % (4649)------------------------------
% 0.21/0.55  % (4663)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (4663)Refutation not found, incomplete strategy% (4663)------------------------------
% 0.21/0.55  % (4663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4663)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4663)Memory used [KB]: 1663
% 0.21/0.55  % (4663)Time elapsed: 0.141 s
% 0.21/0.55  % (4663)------------------------------
% 0.21/0.55  % (4663)------------------------------
% 0.21/0.56  % (4657)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (4657)Refutation not found, incomplete strategy% (4657)------------------------------
% 0.21/0.56  % (4657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4657)Memory used [KB]: 10618
% 0.21/0.56  % (4657)Time elapsed: 0.151 s
% 0.21/0.56  % (4657)------------------------------
% 0.21/0.56  % (4657)------------------------------
% 0.21/0.58  % (4638)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.58  % (4652)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.59  % (4640)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.60  % (4646)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.60  % (4636)Refutation not found, incomplete strategy% (4636)------------------------------
% 0.21/0.60  % (4636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (4636)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (4636)Memory used [KB]: 6140
% 0.21/0.60  % (4636)Time elapsed: 0.208 s
% 0.21/0.60  % (4636)------------------------------
% 0.21/0.60  % (4636)------------------------------
% 0.21/0.61  % SZS output start Proof for theBenchmark
% 0.21/0.61  fof(f1067,plain,(
% 0.21/0.61    $false),
% 0.21/0.61    inference(trivial_inequality_removal,[],[f1065])).
% 0.21/0.61  fof(f1065,plain,(
% 0.21/0.61    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.61    inference(superposition,[],[f44,f798])).
% 0.21/0.61  fof(f798,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.61    inference(backward_demodulation,[],[f84,f797])).
% 0.21/0.61  fof(f797,plain,(
% 0.21/0.61    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3))) )),
% 0.21/0.61    inference(forward_demodulation,[],[f796,f131])).
% 0.21/0.61  fof(f131,plain,(
% 0.21/0.61    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(k3_xboole_0(X1,X2)))) )),
% 0.21/0.61    inference(resolution,[],[f96,f50])).
% 0.21/0.61  fof(f50,plain,(
% 0.21/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f2])).
% 0.21/0.61  fof(f2,axiom,(
% 0.21/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.61  fof(f96,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.61    inference(forward_demodulation,[],[f95,f84])).
% 0.21/0.61  fof(f95,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.21/0.61    inference(forward_demodulation,[],[f94,f47])).
% 0.21/0.61  fof(f47,plain,(
% 0.21/0.61    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.61    inference(cnf_transformation,[],[f17])).
% 0.21/0.61  fof(f17,axiom,(
% 0.21/0.61    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.61  fof(f94,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.21/0.61    inference(resolution,[],[f60,f45])).
% 0.21/0.61  fof(f45,plain,(
% 0.21/0.61    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f13])).
% 0.21/0.61  fof(f13,axiom,(
% 0.21/0.61    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.61  fof(f60,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.21/0.61    inference(cnf_transformation,[],[f34])).
% 0.21/0.61  fof(f34,plain,(
% 0.21/0.61    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(flattening,[],[f33])).
% 0.21/0.61  fof(f33,plain,(
% 0.21/0.61    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f20])).
% 0.21/0.61  fof(f20,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.61  fof(f796,plain,(
% 0.21/0.61    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3)))) )),
% 0.21/0.61    inference(forward_demodulation,[],[f784,f163])).
% 0.21/0.61  fof(f163,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X1,X0)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 0.21/0.61    inference(superposition,[],[f131,f125])).
% 0.21/0.61  fof(f125,plain,(
% 0.21/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.21/0.61    inference(superposition,[],[f74,f53])).
% 0.21/0.61  fof(f53,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f11])).
% 0.21/0.61  fof(f11,axiom,(
% 0.21/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.61  fof(f74,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.21/0.61    inference(superposition,[],[f53,f51])).
% 0.21/0.61  fof(f51,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f4])).
% 0.21/0.61  fof(f4,axiom,(
% 0.21/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.61  fof(f784,plain,(
% 0.21/0.61    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k3_xboole_0(X2,X3))))) )),
% 0.21/0.61    inference(resolution,[],[f143,f72])).
% 0.21/0.61  fof(f72,plain,(
% 0.21/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.61    inference(equality_resolution,[],[f65])).
% 0.21/0.61  fof(f65,plain,(
% 0.21/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.61    inference(cnf_transformation,[],[f43])).
% 0.21/0.61  fof(f43,plain,(
% 0.21/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.61    inference(flattening,[],[f42])).
% 0.21/0.61  fof(f42,plain,(
% 0.21/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.61    inference(nnf_transformation,[],[f1])).
% 0.21/0.61  fof(f1,axiom,(
% 0.21/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.61  fof(f143,plain,(
% 0.21/0.61    ( ! [X26,X24,X25] : (~r1_tarski(k3_xboole_0(X24,X25),X26) | k8_relat_1(X24,k6_relat_1(X25)) = k8_relat_1(X24,k8_relat_1(X25,k6_relat_1(X26)))) )),
% 0.21/0.61    inference(backward_demodulation,[],[f119,f142])).
% 0.21/0.61  fof(f142,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,k6_relat_1(X2)),X1) = k8_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1)))) )),
% 0.21/0.61    inference(forward_demodulation,[],[f141,f84])).
% 0.21/0.61  fof(f141,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X2)),X1)) )),
% 0.21/0.61    inference(forward_demodulation,[],[f139,f105])).
% 0.21/0.61  fof(f105,plain,(
% 0.21/0.61    ( ! [X10,X11,X9] : (k5_relat_1(k6_relat_1(X9),k8_relat_1(X10,k6_relat_1(X11))) = k7_relat_1(k8_relat_1(X10,k6_relat_1(X11)),X9)) )),
% 0.21/0.61    inference(resolution,[],[f93,f56])).
% 0.21/0.61  fof(f56,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f30])).
% 0.21/0.61  fof(f30,plain,(
% 0.21/0.61    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f23])).
% 0.21/0.61  fof(f23,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.61  fof(f93,plain,(
% 0.21/0.61    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.21/0.61    inference(forward_demodulation,[],[f92,f84])).
% 0.21/0.61  fof(f92,plain,(
% 0.21/0.61    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.21/0.61    inference(resolution,[],[f78,f45])).
% 0.21/0.61  fof(f78,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))) )),
% 0.21/0.61    inference(resolution,[],[f63,f45])).
% 0.21/0.61  fof(f63,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f39])).
% 0.21/0.61  fof(f39,plain,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.61    inference(flattening,[],[f38])).
% 0.21/0.61  fof(f38,plain,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.61    inference(ennf_transformation,[],[f12])).
% 0.21/0.61  fof(f12,axiom,(
% 0.21/0.61    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.61  fof(f139,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2)))) )),
% 0.21/0.61    inference(resolution,[],[f100,f45])).
% 0.21/0.61  fof(f100,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(X1,k8_relat_1(X0,k6_relat_1(X2)))) )),
% 0.21/0.61    inference(resolution,[],[f62,f45])).
% 0.21/0.61  fof(f62,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f37])).
% 0.21/0.61  fof(f37,plain,(
% 0.21/0.61    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f15])).
% 0.21/0.61  fof(f15,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).
% 0.21/0.61  fof(f119,plain,(
% 0.21/0.61    ( ! [X26,X24,X25] : (k8_relat_1(X24,k6_relat_1(X25)) = k7_relat_1(k8_relat_1(X24,k6_relat_1(X25)),X26) | ~r1_tarski(k3_xboole_0(X24,X25),X26)) )),
% 0.21/0.61    inference(forward_demodulation,[],[f118,f105])).
% 0.21/0.61  fof(f118,plain,(
% 0.21/0.61    ( ! [X26,X24,X25] : (~r1_tarski(k3_xboole_0(X24,X25),X26) | k8_relat_1(X24,k6_relat_1(X25)) = k5_relat_1(k6_relat_1(X26),k8_relat_1(X24,k6_relat_1(X25)))) )),
% 0.21/0.61    inference(forward_demodulation,[],[f110,f91])).
% 0.21/0.61  fof(f91,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.21/0.61    inference(forward_demodulation,[],[f90,f88])).
% 0.21/0.61  fof(f88,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 0.21/0.61    inference(forward_demodulation,[],[f87,f84])).
% 0.21/0.61  fof(f87,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 0.21/0.61    inference(resolution,[],[f56,f45])).
% 0.21/0.61  fof(f90,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 0.21/0.61    inference(forward_demodulation,[],[f89,f46])).
% 0.21/0.61  fof(f46,plain,(
% 0.21/0.61    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.61    inference(cnf_transformation,[],[f17])).
% 0.21/0.61  fof(f89,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 0.21/0.61    inference(resolution,[],[f57,f45])).
% 0.21/0.61  fof(f57,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f31])).
% 0.21/0.61  fof(f31,plain,(
% 0.21/0.61    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f22])).
% 0.21/0.61  fof(f22,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.61  fof(f110,plain,(
% 0.21/0.61    ( ! [X26,X24,X25] : (~r1_tarski(k1_relat_1(k8_relat_1(X24,k6_relat_1(X25))),X26) | k8_relat_1(X24,k6_relat_1(X25)) = k5_relat_1(k6_relat_1(X26),k8_relat_1(X24,k6_relat_1(X25)))) )),
% 0.21/0.61    inference(resolution,[],[f93,f61])).
% 0.21/0.61  fof(f61,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.21/0.61    inference(cnf_transformation,[],[f36])).
% 0.21/0.61  fof(f36,plain,(
% 0.21/0.61    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(flattening,[],[f35])).
% 0.21/0.61  fof(f35,plain,(
% 0.21/0.61    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f19])).
% 0.21/0.61  fof(f19,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.61  fof(f84,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.21/0.61    inference(resolution,[],[f55,f45])).
% 0.21/0.61  fof(f55,plain,(
% 0.21/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f29])).
% 0.21/0.61  fof(f29,plain,(
% 0.21/0.61    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f14])).
% 0.21/0.61  fof(f14,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.61  fof(f44,plain,(
% 0.21/0.61    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.61    inference(cnf_transformation,[],[f41])).
% 0.21/0.61  fof(f41,plain,(
% 0.21/0.61    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f40])).
% 0.21/0.61  fof(f40,plain,(
% 0.21/0.61    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.61    introduced(choice_axiom,[])).
% 0.21/0.61  fof(f26,plain,(
% 0.21/0.61    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f25])).
% 0.21/0.61  fof(f25,negated_conjecture,(
% 0.21/0.61    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.61    inference(negated_conjecture,[],[f24])).
% 0.21/0.61  fof(f24,conjecture,(
% 0.21/0.61    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.61  % SZS output end Proof for theBenchmark
% 1.95/0.61  % (4640)------------------------------
% 1.95/0.61  % (4640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.61  % (4640)Termination reason: Refutation
% 1.95/0.61  
% 1.95/0.61  % (4640)Memory used [KB]: 2430
% 1.95/0.61  % (4640)Time elapsed: 0.175 s
% 1.95/0.61  % (4640)------------------------------
% 1.95/0.61  % (4640)------------------------------
% 1.95/0.62  % (4632)Success in time 0.251 s
%------------------------------------------------------------------------------
