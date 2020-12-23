%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:45 EST 2020

% Result     : Theorem 3.00s
% Output     : Refutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 403 expanded)
%              Number of leaves         :   17 ( 109 expanded)
%              Depth                    :   17
%              Number of atoms          :  169 ( 899 expanded)
%              Number of equality atoms :   70 ( 213 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13185)Time limit reached!
% (13185)------------------------------
% (13185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13185)Termination reason: Time limit

% (13185)Memory used [KB]: 7419
% (13185)Time elapsed: 0.415 s
% (13185)------------------------------
% (13185)------------------------------
fof(f4723,plain,(
    $false ),
    inference(resolution,[],[f4690,f59])).

fof(f59,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f53])).

fof(f53,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f4690,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f4613,f4614])).

fof(f4614,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f2871,f4598])).

fof(f4598,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f4597,f126])).

fof(f126,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f125,f74])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f125,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f123,f75])).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f123,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f64,f85])).

fof(f85,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f4597,plain,(
    k10_relat_1(k6_relat_1(sK0),sK0) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f4588,f2058])).

fof(f2058,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(superposition,[],[f1889,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1889,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f1888,f302])).

fof(f302,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f300,f177])).

fof(f177,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),sK1) = k7_relat_1(sK1,X0) ),
    inference(resolution,[],[f79,f57])).

fof(f57,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f300,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f246,f85])).

fof(f246,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f63,f57])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f1888,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f1878,f324])).

fof(f324,plain,(
    ! [X0] : k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f280,f122])).

fof(f122,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(resolution,[],[f64,f57])).

fof(f280,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f92,f57])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f1878,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f351,f122])).

fof(f351,plain,(
    ! [X2,X1] : k10_relat_1(k7_relat_1(sK1,X1),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK1,X2)) ),
    inference(forward_demodulation,[],[f349,f177])).

fof(f349,plain,(
    ! [X2,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK1,X2)) ),
    inference(resolution,[],[f287,f85])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f61,f57])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f4588,plain,(
    k10_relat_1(k6_relat_1(sK0),sK0) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) ),
    inference(superposition,[],[f938,f1268])).

fof(f1268,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f897,f85])).

fof(f897,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f876,f58])).

fof(f58,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f876,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f245,f178])).

fof(f178,plain,(
    ! [X2,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(resolution,[],[f79,f85])).

fof(f245,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f73,f74])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f938,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[],[f281,f126])).

fof(f281,plain,(
    ! [X4,X2,X3] : k10_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k1_setfam_1(k2_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))) ),
    inference(resolution,[],[f92,f85])).

fof(f2871,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f2868,f968])).

fof(f968,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f130,f57])).

fof(f130,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f66,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f2868,plain,(
    ! [X0] : k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f1409,f57])).

fof(f1409,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(k7_relat_1(sK1,X1),k1_relat_1(k7_relat_1(X0,X1))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f274,f57])).

fof(f274,plain,(
    ! [X26,X27,X25] :
      ( ~ v1_relat_1(X27)
      | ~ v1_relat_1(X25)
      | k9_relat_1(k7_relat_1(X27,X26),k1_relat_1(k7_relat_1(X25,X26))) = k9_relat_1(X27,k1_relat_1(k7_relat_1(X25,X26))) ) ),
    inference(resolution,[],[f65,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0)
      | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f4613,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0)))) ),
    inference(superposition,[],[f2267,f4598])).

fof(f2267,plain,(
    ! [X2] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X2)))) ),
    inference(superposition,[],[f331,f965])).

fof(f965,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f124,f57])).

fof(f124,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2))) ) ),
    inference(resolution,[],[f64,f76])).

fof(f331,plain,(
    ! [X4,X5] : r1_tarski(k10_relat_1(k7_relat_1(sK1,X4),X5),k10_relat_1(sK1,X5)) ),
    inference(superposition,[],[f107,f280])).

fof(f107,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f94,f87])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f78,f77])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:33:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.52  % (13198)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (13206)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (13188)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (13190)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (13196)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (13187)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (13184)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (13201)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (13204)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (13186)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (13212)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (13208)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (13183)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (13211)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (13185)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (13203)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (13194)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (13192)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (13213)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (13197)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (13199)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (13210)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (13200)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (13193)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (13195)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (13191)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.57  % (13202)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (13209)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.58  % (13189)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.60  % (13205)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.20/0.70  % (13186)Refutation not found, incomplete strategy% (13186)------------------------------
% 2.20/0.70  % (13186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.70  % (13186)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.70  
% 2.20/0.70  % (13186)Memory used [KB]: 6140
% 2.20/0.70  % (13186)Time elapsed: 0.284 s
% 2.20/0.70  % (13186)------------------------------
% 2.20/0.70  % (13186)------------------------------
% 3.00/0.83  % (13208)Time limit reached!
% 3.00/0.83  % (13208)------------------------------
% 3.00/0.83  % (13208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.00/0.83  % (13208)Termination reason: Time limit
% 3.00/0.83  % (13208)Termination phase: Saturation
% 3.00/0.83  
% 3.00/0.83  % (13208)Memory used [KB]: 13048
% 3.00/0.83  % (13208)Time elapsed: 0.419 s
% 3.00/0.83  % (13208)------------------------------
% 3.00/0.83  % (13208)------------------------------
% 3.00/0.83  % (13188)Refutation found. Thanks to Tanya!
% 3.00/0.83  % SZS status Theorem for theBenchmark
% 3.00/0.83  % SZS output start Proof for theBenchmark
% 3.57/0.83  % (13185)Time limit reached!
% 3.57/0.83  % (13185)------------------------------
% 3.57/0.83  % (13185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.57/0.83  % (13185)Termination reason: Time limit
% 3.57/0.83  
% 3.57/0.83  % (13185)Memory used [KB]: 7419
% 3.57/0.83  % (13185)Time elapsed: 0.415 s
% 3.57/0.83  % (13185)------------------------------
% 3.57/0.83  % (13185)------------------------------
% 3.57/0.85  fof(f4723,plain,(
% 3.57/0.85    $false),
% 3.57/0.85    inference(resolution,[],[f4690,f59])).
% 3.57/0.85  fof(f59,plain,(
% 3.57/0.85    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 3.57/0.85    inference(cnf_transformation,[],[f54])).
% 3.57/0.85  fof(f54,plain,(
% 3.57/0.85    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 3.57/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f53])).
% 3.57/0.85  fof(f53,plain,(
% 3.57/0.85    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 3.57/0.85    introduced(choice_axiom,[])).
% 3.57/0.85  fof(f32,plain,(
% 3.57/0.85    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 3.57/0.85    inference(flattening,[],[f31])).
% 3.57/0.85  fof(f31,plain,(
% 3.57/0.85    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 3.57/0.85    inference(ennf_transformation,[],[f30])).
% 3.57/0.85  fof(f30,negated_conjecture,(
% 3.57/0.85    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.57/0.85    inference(negated_conjecture,[],[f29])).
% 3.57/0.85  fof(f29,conjecture,(
% 3.57/0.85    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 3.57/0.85  fof(f4690,plain,(
% 3.57/0.85    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 3.57/0.85    inference(backward_demodulation,[],[f4613,f4614])).
% 3.57/0.85  fof(f4614,plain,(
% 3.57/0.85    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 3.57/0.85    inference(superposition,[],[f2871,f4598])).
% 3.57/0.85  fof(f4598,plain,(
% 3.57/0.85    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 3.57/0.85    inference(forward_demodulation,[],[f4597,f126])).
% 3.57/0.85  fof(f126,plain,(
% 3.57/0.85    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 3.57/0.85    inference(forward_demodulation,[],[f125,f74])).
% 3.57/0.85  fof(f74,plain,(
% 3.57/0.85    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.57/0.85    inference(cnf_transformation,[],[f22])).
% 3.57/0.85  fof(f22,axiom,(
% 3.57/0.85    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.57/0.85  fof(f125,plain,(
% 3.57/0.85    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 3.57/0.85    inference(forward_demodulation,[],[f123,f75])).
% 3.57/0.85  fof(f75,plain,(
% 3.57/0.85    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.57/0.85    inference(cnf_transformation,[],[f22])).
% 3.57/0.85  fof(f123,plain,(
% 3.57/0.85    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 3.57/0.85    inference(resolution,[],[f64,f85])).
% 3.57/0.85  fof(f85,plain,(
% 3.57/0.85    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.57/0.85    inference(cnf_transformation,[],[f26])).
% 3.57/0.85  fof(f26,axiom,(
% 3.57/0.85    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 3.57/0.85  fof(f64,plain,(
% 3.57/0.85    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 3.57/0.85    inference(cnf_transformation,[],[f37])).
% 3.57/0.85  fof(f37,plain,(
% 3.57/0.85    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.57/0.85    inference(ennf_transformation,[],[f19])).
% 3.57/0.85  fof(f19,axiom,(
% 3.57/0.85    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 3.57/0.85  fof(f4597,plain,(
% 3.57/0.85    k10_relat_1(k6_relat_1(sK0),sK0) = k1_relat_1(k7_relat_1(sK1,sK0))),
% 3.57/0.85    inference(forward_demodulation,[],[f4588,f2058])).
% 3.57/0.85  fof(f2058,plain,(
% 3.57/0.85    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 3.57/0.85    inference(superposition,[],[f1889,f87])).
% 3.57/0.85  fof(f87,plain,(
% 3.57/0.85    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.57/0.85    inference(cnf_transformation,[],[f12])).
% 3.57/0.85  fof(f12,axiom,(
% 3.57/0.85    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.57/0.85  fof(f1889,plain,(
% 3.57/0.85    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 3.57/0.85    inference(forward_demodulation,[],[f1888,f302])).
% 3.57/0.85  fof(f302,plain,(
% 3.57/0.85    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k7_relat_1(sK1,X0))) )),
% 3.57/0.85    inference(forward_demodulation,[],[f300,f177])).
% 3.57/0.85  fof(f177,plain,(
% 3.57/0.85    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),sK1) = k7_relat_1(sK1,X0)) )),
% 3.57/0.85    inference(resolution,[],[f79,f57])).
% 3.57/0.85  fof(f57,plain,(
% 3.57/0.85    v1_relat_1(sK1)),
% 3.57/0.85    inference(cnf_transformation,[],[f54])).
% 3.57/0.85  fof(f79,plain,(
% 3.57/0.85    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 3.57/0.85    inference(cnf_transformation,[],[f46])).
% 3.57/0.85  fof(f46,plain,(
% 3.57/0.85    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.57/0.85    inference(ennf_transformation,[],[f25])).
% 3.57/0.85  fof(f25,axiom,(
% 3.57/0.85    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 3.57/0.85  fof(f300,plain,(
% 3.57/0.85    ( ! [X0] : (k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) )),
% 3.57/0.85    inference(resolution,[],[f246,f85])).
% 3.57/0.85  fof(f246,plain,(
% 3.57/0.85    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))) )),
% 3.57/0.85    inference(resolution,[],[f63,f57])).
% 3.57/0.85  fof(f63,plain,(
% 3.57/0.85    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 3.57/0.85    inference(cnf_transformation,[],[f36])).
% 3.57/0.85  fof(f36,plain,(
% 3.57/0.85    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.57/0.85    inference(ennf_transformation,[],[f21])).
% 3.57/0.85  fof(f21,axiom,(
% 3.57/0.85    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 3.57/0.85  fof(f1888,plain,(
% 3.57/0.85    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 3.57/0.85    inference(forward_demodulation,[],[f1878,f324])).
% 3.57/0.85  fof(f324,plain,(
% 3.57/0.85    ( ! [X0] : (k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 3.57/0.85    inference(superposition,[],[f280,f122])).
% 3.57/0.85  fof(f122,plain,(
% 3.57/0.85    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 3.57/0.85    inference(resolution,[],[f64,f57])).
% 3.57/0.85  fof(f280,plain,(
% 3.57/0.85    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1)))) )),
% 3.57/0.85    inference(resolution,[],[f92,f57])).
% 3.57/0.85  fof(f92,plain,(
% 3.57/0.85    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) )),
% 3.57/0.85    inference(definition_unfolding,[],[f60,f77])).
% 3.57/0.85  fof(f77,plain,(
% 3.57/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.57/0.85    inference(cnf_transformation,[],[f14])).
% 3.57/0.85  fof(f14,axiom,(
% 3.57/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.57/0.85  fof(f60,plain,(
% 3.57/0.85    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.57/0.85    inference(cnf_transformation,[],[f33])).
% 3.57/0.85  fof(f33,plain,(
% 3.57/0.85    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.57/0.85    inference(ennf_transformation,[],[f28])).
% 3.57/0.85  fof(f28,axiom,(
% 3.57/0.85    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 3.57/0.85  fof(f1878,plain,(
% 3.57/0.85    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1))) )),
% 3.57/0.85    inference(superposition,[],[f351,f122])).
% 3.57/0.85  fof(f351,plain,(
% 3.57/0.85    ( ! [X2,X1] : (k10_relat_1(k7_relat_1(sK1,X1),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK1,X2))) )),
% 3.57/0.85    inference(forward_demodulation,[],[f349,f177])).
% 3.57/0.85  fof(f349,plain,(
% 3.57/0.85    ( ! [X2,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK1,X2))) )),
% 3.57/0.85    inference(resolution,[],[f287,f85])).
% 3.57/0.85  fof(f287,plain,(
% 3.57/0.85    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1))) )),
% 3.57/0.85    inference(resolution,[],[f61,f57])).
% 3.57/0.85  fof(f61,plain,(
% 3.57/0.85    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 3.57/0.85    inference(cnf_transformation,[],[f34])).
% 3.57/0.85  fof(f34,plain,(
% 3.57/0.85    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.57/0.85    inference(ennf_transformation,[],[f20])).
% 3.57/0.85  fof(f20,axiom,(
% 3.57/0.85    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 3.57/0.85  fof(f4588,plain,(
% 3.57/0.85    k10_relat_1(k6_relat_1(sK0),sK0) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))),
% 3.57/0.85    inference(superposition,[],[f938,f1268])).
% 3.57/0.85  fof(f1268,plain,(
% 3.57/0.85    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 3.57/0.85    inference(resolution,[],[f897,f85])).
% 3.57/0.85  fof(f897,plain,(
% 3.57/0.85    ~v1_relat_1(k6_relat_1(sK0)) | k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 3.57/0.85    inference(resolution,[],[f876,f58])).
% 3.57/0.85  fof(f58,plain,(
% 3.57/0.85    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.57/0.85    inference(cnf_transformation,[],[f54])).
% 3.57/0.85  fof(f876,plain,(
% 3.57/0.85    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 3.57/0.85    inference(forward_demodulation,[],[f245,f178])).
% 3.57/0.85  fof(f178,plain,(
% 3.57/0.85    ( ! [X2,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X2),X1)) )),
% 3.57/0.85    inference(resolution,[],[f79,f85])).
% 3.57/0.85  fof(f245,plain,(
% 3.57/0.85    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.57/0.85    inference(superposition,[],[f73,f74])).
% 3.57/0.85  fof(f73,plain,(
% 3.57/0.85    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 3.57/0.85    inference(cnf_transformation,[],[f44])).
% 3.57/0.85  fof(f44,plain,(
% 3.57/0.85    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.57/0.85    inference(flattening,[],[f43])).
% 3.57/0.85  fof(f43,plain,(
% 3.57/0.85    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.57/0.85    inference(ennf_transformation,[],[f23])).
% 3.57/0.85  fof(f23,axiom,(
% 3.57/0.85    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 3.57/0.85  fof(f938,plain,(
% 3.57/0.85    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 3.57/0.85    inference(superposition,[],[f281,f126])).
% 3.57/0.85  fof(f281,plain,(
% 3.57/0.85    ( ! [X4,X2,X3] : (k10_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k1_setfam_1(k2_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)))) )),
% 3.57/0.85    inference(resolution,[],[f92,f85])).
% 3.57/0.85  fof(f2871,plain,(
% 3.57/0.85    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 3.57/0.85    inference(forward_demodulation,[],[f2868,f968])).
% 3.57/0.85  fof(f968,plain,(
% 3.57/0.85    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 3.57/0.85    inference(resolution,[],[f130,f57])).
% 3.57/0.85  fof(f130,plain,(
% 3.57/0.85    ( ! [X2,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(k7_relat_1(X1,X2),k1_relat_1(k7_relat_1(X1,X2)))) )),
% 3.57/0.85    inference(resolution,[],[f66,f76])).
% 3.57/0.85  fof(f76,plain,(
% 3.57/0.85    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.57/0.85    inference(cnf_transformation,[],[f45])).
% 3.57/0.85  fof(f45,plain,(
% 3.57/0.85    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.57/0.85    inference(ennf_transformation,[],[f15])).
% 3.57/0.85  fof(f15,axiom,(
% 3.57/0.85    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 3.57/0.85  fof(f66,plain,(
% 3.57/0.85    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 3.57/0.85    inference(cnf_transformation,[],[f39])).
% 3.57/0.85  fof(f39,plain,(
% 3.57/0.85    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.57/0.85    inference(ennf_transformation,[],[f16])).
% 3.57/0.85  fof(f16,axiom,(
% 3.57/0.85    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 3.57/0.85  fof(f2868,plain,(
% 3.57/0.85    ( ! [X0] : (k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 3.57/0.85    inference(resolution,[],[f1409,f57])).
% 3.57/0.85  fof(f1409,plain,(
% 3.57/0.85    ( ! [X0,X1] : (~v1_relat_1(X0) | k9_relat_1(k7_relat_1(sK1,X1),k1_relat_1(k7_relat_1(X0,X1))) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(X0,X1)))) )),
% 3.57/0.85    inference(resolution,[],[f274,f57])).
% 3.57/0.85  fof(f274,plain,(
% 3.57/0.85    ( ! [X26,X27,X25] : (~v1_relat_1(X27) | ~v1_relat_1(X25) | k9_relat_1(k7_relat_1(X27,X26),k1_relat_1(k7_relat_1(X25,X26))) = k9_relat_1(X27,k1_relat_1(k7_relat_1(X25,X26)))) )),
% 3.57/0.85    inference(resolution,[],[f65,f71])).
% 3.57/0.85  fof(f71,plain,(
% 3.57/0.85    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.57/0.85    inference(cnf_transformation,[],[f42])).
% 3.57/0.85  fof(f42,plain,(
% 3.57/0.85    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.57/0.85    inference(ennf_transformation,[],[f24])).
% 3.57/0.85  fof(f24,axiom,(
% 3.57/0.85    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 3.57/0.85  fof(f65,plain,(
% 3.57/0.85    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~v1_relat_1(X0) | k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)) )),
% 3.57/0.85    inference(cnf_transformation,[],[f38])).
% 3.57/0.85  fof(f38,plain,(
% 3.57/0.85    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 3.57/0.85    inference(ennf_transformation,[],[f17])).
% 3.57/0.85  fof(f17,axiom,(
% 3.57/0.85    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 3.57/0.85  fof(f4613,plain,(
% 3.57/0.85    r1_tarski(sK0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,sK0))))),
% 3.57/0.85    inference(superposition,[],[f2267,f4598])).
% 3.57/0.85  fof(f2267,plain,(
% 3.57/0.85    ( ! [X2] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X2))))) )),
% 3.57/0.85    inference(superposition,[],[f331,f965])).
% 3.57/0.85  fof(f965,plain,(
% 3.57/0.85    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) )),
% 3.57/0.85    inference(resolution,[],[f124,f57])).
% 3.57/0.85  fof(f124,plain,(
% 3.57/0.85    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X2),k2_relat_1(k7_relat_1(X1,X2)))) )),
% 3.57/0.85    inference(resolution,[],[f64,f76])).
% 3.57/0.85  fof(f331,plain,(
% 3.57/0.85    ( ! [X4,X5] : (r1_tarski(k10_relat_1(k7_relat_1(sK1,X4),X5),k10_relat_1(sK1,X5))) )),
% 3.57/0.85    inference(superposition,[],[f107,f280])).
% 3.57/0.85  fof(f107,plain,(
% 3.57/0.85    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 3.57/0.85    inference(superposition,[],[f94,f87])).
% 3.57/0.85  fof(f94,plain,(
% 3.57/0.85    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 3.57/0.85    inference(definition_unfolding,[],[f78,f77])).
% 3.57/0.85  fof(f78,plain,(
% 3.57/0.85    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.57/0.85    inference(cnf_transformation,[],[f3])).
% 3.57/0.85  fof(f3,axiom,(
% 3.57/0.85    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.57/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.57/0.85  % SZS output end Proof for theBenchmark
% 3.57/0.85  % (13188)------------------------------
% 3.57/0.85  % (13188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.57/0.85  % (13188)Termination reason: Refutation
% 3.57/0.85  
% 3.57/0.85  % (13188)Memory used [KB]: 3837
% 3.57/0.85  % (13188)Time elapsed: 0.415 s
% 3.57/0.85  % (13188)------------------------------
% 3.57/0.85  % (13188)------------------------------
% 3.57/0.86  % (13182)Success in time 0.484 s
%------------------------------------------------------------------------------
