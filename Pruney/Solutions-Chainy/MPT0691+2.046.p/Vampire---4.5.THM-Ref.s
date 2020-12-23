%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:51 EST 2020

% Result     : Theorem 2.28s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 146 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   19
%              Number of atoms          :  194 ( 308 expanded)
%              Number of equality atoms :   44 (  62 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f765,f1449])).

fof(f1449,plain,(
    ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f1448])).

fof(f1448,plain,
    ( $false
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f1447,f34])).

fof(f34,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f1447,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f1433,f70])).

fof(f70,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f69,f38])).

fof(f38,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f69,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f67,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f1433,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(sK0),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_10 ),
    inference(superposition,[],[f126,f1404])).

fof(f1404,plain,
    ( sK0 = k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl2_10 ),
    inference(superposition,[],[f1301,f774])).

fof(f774,plain,
    ( sK0 = k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK1),k9_relat_1(sK1,sK0))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f773,f746])).

fof(f746,plain,(
    sK0 = k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(resolution,[],[f673,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f673,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | k1_relat_1(k5_relat_1(k6_relat_1(X1),sK1)) = X1 ) ),
    inference(backward_demodulation,[],[f230,f670])).

fof(f670,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) ),
    inference(resolution,[],[f665,f35])).

fof(f665,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f230,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | k10_relat_1(k6_relat_1(X1),k1_relat_1(sK1)) = X1 ) ),
    inference(resolution,[],[f228,f85])).

fof(f85,plain,(
    ! [X2] :
      ( r1_tarski(X2,k1_relat_1(sK1))
      | ~ r1_tarski(X2,sK0) ) ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f228,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k10_relat_1(k6_relat_1(X10),X11) = X10 ) ),
    inference(subsumption_resolution,[],[f224,f55])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f54,f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f43,f37])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f224,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(k10_relat_1(k6_relat_1(X10),X11),X10)
      | k10_relat_1(k6_relat_1(X10),X11) = X10 ) ),
    inference(resolution,[],[f201,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f201,plain,(
    ! [X2,X1] :
      ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
      | ~ r1_tarski(X1,X2) ) ),
    inference(subsumption_resolution,[],[f197,f35])).

fof(f197,plain,(
    ! [X2,X1] :
      ( r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f50,f60])).

fof(f60,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f59,f37])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f57,f38])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f773,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK1),k9_relat_1(sK1,sK0))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f766,f368])).

fof(f368,plain,(
    ! [X0] : k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k9_relat_1(sK1,X0) ),
    inference(forward_demodulation,[],[f366,f38])).

fof(f366,plain,(
    ! [X0] : k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k9_relat_1(sK1,k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f362,f35])).

fof(f362,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,sK1)) = k9_relat_1(sK1,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f41,f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f766,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK1),k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl2_10 ),
    inference(resolution,[],[f756,f39])).

fof(f756,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f755])).

fof(f755,plain,
    ( spl2_10
  <=> v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f1301,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),k10_relat_1(sK1,X2)) = k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),X2) ),
    inference(resolution,[],[f1294,f35])).

fof(f1294,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(f126,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),X1) ),
    inference(subsumption_resolution,[],[f125,f35])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),X1) ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f765,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f764])).

fof(f764,plain,
    ( $false
    | spl2_10 ),
    inference(subsumption_resolution,[],[f763,f35])).

fof(f763,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_10 ),
    inference(subsumption_resolution,[],[f762,f32])).

fof(f762,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_10 ),
    inference(resolution,[],[f757,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f757,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (13479)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.46  % (13471)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (13461)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (13459)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (13466)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (13474)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (13469)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (13467)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (13475)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (13460)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (13457)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (13470)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (13462)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (13468)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (13465)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (13481)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (13458)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (13476)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (13480)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (13456)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (13464)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (13472)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (13463)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (13473)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (13478)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (13477)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 2.28/0.68  % (13478)Refutation found. Thanks to Tanya!
% 2.28/0.68  % SZS status Theorem for theBenchmark
% 2.28/0.68  % SZS output start Proof for theBenchmark
% 2.28/0.68  fof(f1455,plain,(
% 2.28/0.68    $false),
% 2.28/0.68    inference(avatar_sat_refutation,[],[f765,f1449])).
% 2.28/0.68  fof(f1449,plain,(
% 2.28/0.68    ~spl2_10),
% 2.28/0.68    inference(avatar_contradiction_clause,[],[f1448])).
% 2.28/0.68  fof(f1448,plain,(
% 2.28/0.68    $false | ~spl2_10),
% 2.28/0.68    inference(subsumption_resolution,[],[f1447,f34])).
% 2.28/0.68  fof(f34,plain,(
% 2.28/0.68    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.28/0.68    inference(cnf_transformation,[],[f17])).
% 2.28/0.68  fof(f17,plain,(
% 2.28/0.68    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 2.28/0.68    inference(flattening,[],[f16])).
% 2.28/0.68  fof(f16,plain,(
% 2.28/0.68    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.28/0.68    inference(ennf_transformation,[],[f15])).
% 2.28/0.68  fof(f15,negated_conjecture,(
% 2.28/0.68    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.28/0.68    inference(negated_conjecture,[],[f14])).
% 2.28/0.68  fof(f14,conjecture,(
% 2.28/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.28/0.68  fof(f1447,plain,(
% 2.28/0.68    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~spl2_10),
% 2.28/0.68    inference(forward_demodulation,[],[f1433,f70])).
% 2.28/0.68  fof(f70,plain,(
% 2.28/0.68    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.28/0.68    inference(forward_demodulation,[],[f69,f38])).
% 2.28/0.68  fof(f38,plain,(
% 2.28/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.28/0.68    inference(cnf_transformation,[],[f11])).
% 2.28/0.68  fof(f11,axiom,(
% 2.28/0.68    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.28/0.68  fof(f69,plain,(
% 2.28/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 2.28/0.68    inference(forward_demodulation,[],[f67,f37])).
% 2.28/0.68  fof(f37,plain,(
% 2.28/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.28/0.68    inference(cnf_transformation,[],[f11])).
% 2.28/0.68  fof(f67,plain,(
% 2.28/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 2.28/0.68    inference(resolution,[],[f40,f35])).
% 2.28/0.68  fof(f35,plain,(
% 2.28/0.68    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.28/0.68    inference(cnf_transformation,[],[f12])).
% 2.28/0.68  fof(f12,axiom,(
% 2.28/0.68    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.28/0.68  fof(f40,plain,(
% 2.28/0.68    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.28/0.68    inference(cnf_transformation,[],[f19])).
% 2.28/0.68  fof(f19,plain,(
% 2.28/0.68    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.28/0.68    inference(ennf_transformation,[],[f4])).
% 2.28/0.68  fof(f4,axiom,(
% 2.28/0.68    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 2.28/0.68  fof(f1433,plain,(
% 2.28/0.68    r1_tarski(k9_relat_1(k6_relat_1(sK0),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~spl2_10),
% 2.28/0.68    inference(superposition,[],[f126,f1404])).
% 2.28/0.68  fof(f1404,plain,(
% 2.28/0.68    sK0 = k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~spl2_10),
% 2.28/0.68    inference(superposition,[],[f1301,f774])).
% 2.28/0.68  fof(f774,plain,(
% 2.28/0.68    sK0 = k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK1),k9_relat_1(sK1,sK0)) | ~spl2_10),
% 2.28/0.68    inference(forward_demodulation,[],[f773,f746])).
% 2.28/0.68  fof(f746,plain,(
% 2.28/0.68    sK0 = k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 2.28/0.68    inference(resolution,[],[f673,f52])).
% 2.28/0.68  fof(f52,plain,(
% 2.28/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.28/0.68    inference(equality_resolution,[],[f48])).
% 2.28/0.68  fof(f48,plain,(
% 2.28/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.28/0.68    inference(cnf_transformation,[],[f1])).
% 2.28/0.68  fof(f1,axiom,(
% 2.28/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.28/0.68  fof(f673,plain,(
% 2.28/0.68    ( ! [X1] : (~r1_tarski(X1,sK0) | k1_relat_1(k5_relat_1(k6_relat_1(X1),sK1)) = X1) )),
% 2.28/0.68    inference(backward_demodulation,[],[f230,f670])).
% 2.28/0.68  fof(f670,plain,(
% 2.28/0.68    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),sK1))) )),
% 2.28/0.68    inference(resolution,[],[f665,f35])).
% 2.28/0.68  fof(f665,plain,(
% 2.28/0.68    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))) )),
% 2.28/0.68    inference(resolution,[],[f42,f32])).
% 2.28/0.68  fof(f32,plain,(
% 2.28/0.68    v1_relat_1(sK1)),
% 2.28/0.68    inference(cnf_transformation,[],[f17])).
% 2.28/0.68  fof(f42,plain,(
% 2.28/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 2.28/0.68    inference(cnf_transformation,[],[f21])).
% 2.28/0.68  fof(f21,plain,(
% 2.28/0.68    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.28/0.68    inference(ennf_transformation,[],[f10])).
% 2.28/0.68  fof(f10,axiom,(
% 2.28/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.28/0.68  fof(f230,plain,(
% 2.28/0.68    ( ! [X1] : (~r1_tarski(X1,sK0) | k10_relat_1(k6_relat_1(X1),k1_relat_1(sK1)) = X1) )),
% 2.28/0.68    inference(resolution,[],[f228,f85])).
% 2.28/0.68  fof(f85,plain,(
% 2.28/0.68    ( ! [X2] : (r1_tarski(X2,k1_relat_1(sK1)) | ~r1_tarski(X2,sK0)) )),
% 2.28/0.68    inference(resolution,[],[f51,f33])).
% 2.28/0.68  fof(f33,plain,(
% 2.28/0.68    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.28/0.68    inference(cnf_transformation,[],[f17])).
% 2.28/0.68  fof(f51,plain,(
% 2.28/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.28/0.68    inference(cnf_transformation,[],[f31])).
% 2.28/0.68  fof(f31,plain,(
% 2.28/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.28/0.68    inference(flattening,[],[f30])).
% 2.28/0.68  fof(f30,plain,(
% 2.28/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.28/0.68    inference(ennf_transformation,[],[f2])).
% 2.28/0.68  fof(f2,axiom,(
% 2.28/0.68    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.28/0.68  fof(f228,plain,(
% 2.28/0.68    ( ! [X10,X11] : (~r1_tarski(X10,X11) | k10_relat_1(k6_relat_1(X10),X11) = X10) )),
% 2.28/0.68    inference(subsumption_resolution,[],[f224,f55])).
% 2.28/0.68  fof(f55,plain,(
% 2.28/0.68    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.28/0.68    inference(subsumption_resolution,[],[f54,f35])).
% 2.28/0.68  fof(f54,plain,(
% 2.28/0.68    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.28/0.68    inference(superposition,[],[f43,f37])).
% 2.28/0.68  fof(f43,plain,(
% 2.28/0.68    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.28/0.68    inference(cnf_transformation,[],[f22])).
% 2.28/0.68  fof(f22,plain,(
% 2.28/0.68    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.28/0.68    inference(ennf_transformation,[],[f6])).
% 2.28/0.68  fof(f6,axiom,(
% 2.28/0.68    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 2.28/0.68  fof(f224,plain,(
% 2.28/0.68    ( ! [X10,X11] : (~r1_tarski(X10,X11) | ~r1_tarski(k10_relat_1(k6_relat_1(X10),X11),X10) | k10_relat_1(k6_relat_1(X10),X11) = X10) )),
% 2.28/0.68    inference(resolution,[],[f201,f49])).
% 2.28/0.68  fof(f49,plain,(
% 2.28/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.28/0.68    inference(cnf_transformation,[],[f1])).
% 2.28/0.68  fof(f201,plain,(
% 2.28/0.68    ( ! [X2,X1] : (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2)) | ~r1_tarski(X1,X2)) )),
% 2.28/0.68    inference(subsumption_resolution,[],[f197,f35])).
% 2.28/0.68  fof(f197,plain,(
% 2.28/0.68    ( ! [X2,X1] : (r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.28/0.68    inference(superposition,[],[f50,f60])).
% 2.28/0.68  fof(f60,plain,(
% 2.28/0.68    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.28/0.68    inference(forward_demodulation,[],[f59,f37])).
% 2.28/0.68  fof(f59,plain,(
% 2.28/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 2.28/0.68    inference(forward_demodulation,[],[f57,f38])).
% 2.28/0.68  fof(f57,plain,(
% 2.28/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 2.28/0.68    inference(resolution,[],[f39,f35])).
% 2.28/0.68  fof(f39,plain,(
% 2.28/0.68    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 2.28/0.68    inference(cnf_transformation,[],[f18])).
% 2.28/0.68  fof(f18,plain,(
% 2.28/0.68    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.28/0.68    inference(ennf_transformation,[],[f7])).
% 2.28/0.68  fof(f7,axiom,(
% 2.28/0.68    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.28/0.68  fof(f50,plain,(
% 2.28/0.68    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 2.28/0.68    inference(cnf_transformation,[],[f29])).
% 2.28/0.68  fof(f29,plain,(
% 2.28/0.68    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 2.28/0.68    inference(flattening,[],[f28])).
% 2.28/0.68  fof(f28,plain,(
% 2.28/0.68    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 2.28/0.68    inference(ennf_transformation,[],[f8])).
% 2.28/0.68  fof(f8,axiom,(
% 2.28/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 2.28/0.68  fof(f773,plain,(
% 2.28/0.68    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK1),k9_relat_1(sK1,sK0)) | ~spl2_10),
% 2.28/0.68    inference(forward_demodulation,[],[f766,f368])).
% 2.28/0.68  fof(f368,plain,(
% 2.28/0.68    ( ! [X0] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k9_relat_1(sK1,X0)) )),
% 2.28/0.68    inference(forward_demodulation,[],[f366,f38])).
% 2.28/0.68  fof(f366,plain,(
% 2.28/0.68    ( ! [X0] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k9_relat_1(sK1,k2_relat_1(k6_relat_1(X0)))) )),
% 2.28/0.68    inference(resolution,[],[f362,f35])).
% 2.28/0.68  fof(f362,plain,(
% 2.28/0.68    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,sK1)) = k9_relat_1(sK1,k2_relat_1(X0))) )),
% 2.28/0.68    inference(resolution,[],[f41,f32])).
% 2.28/0.68  fof(f41,plain,(
% 2.28/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 2.28/0.68    inference(cnf_transformation,[],[f20])).
% 2.28/0.68  fof(f20,plain,(
% 2.28/0.68    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.28/0.68    inference(ennf_transformation,[],[f5])).
% 2.28/0.68  fof(f5,axiom,(
% 2.28/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 2.28/0.68  fof(f766,plain,(
% 2.28/0.68    k1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) = k10_relat_1(k5_relat_1(k6_relat_1(sK0),sK1),k2_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))) | ~spl2_10),
% 2.28/0.68    inference(resolution,[],[f756,f39])).
% 2.28/0.68  fof(f756,plain,(
% 2.28/0.68    v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | ~spl2_10),
% 2.28/0.68    inference(avatar_component_clause,[],[f755])).
% 2.28/0.68  fof(f755,plain,(
% 2.28/0.68    spl2_10 <=> v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))),
% 2.28/0.68    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.28/0.68  fof(f1301,plain,(
% 2.28/0.68    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),k10_relat_1(sK1,X2)) = k10_relat_1(k5_relat_1(k6_relat_1(X1),sK1),X2)) )),
% 2.28/0.68    inference(resolution,[],[f1294,f35])).
% 2.28/0.68  fof(f1294,plain,(
% 2.28/0.68    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(X0,sK1),X1) = k10_relat_1(X0,k10_relat_1(sK1,X1))) )),
% 2.28/0.68    inference(resolution,[],[f44,f32])).
% 2.28/0.68  fof(f44,plain,(
% 2.28/0.68    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 2.28/0.68    inference(cnf_transformation,[],[f23])).
% 2.28/0.68  fof(f23,plain,(
% 2.28/0.68    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.28/0.68    inference(ennf_transformation,[],[f9])).
% 2.28/0.68  fof(f9,axiom,(
% 2.28/0.68    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
% 2.28/0.68  fof(f126,plain,(
% 2.28/0.68    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 2.28/0.68    inference(subsumption_resolution,[],[f125,f35])).
% 2.28/0.68  fof(f125,plain,(
% 2.28/0.68    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | r1_tarski(k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 2.28/0.68    inference(resolution,[],[f45,f36])).
% 2.28/0.68  fof(f36,plain,(
% 2.28/0.68    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.28/0.68    inference(cnf_transformation,[],[f12])).
% 2.28/0.68  fof(f45,plain,(
% 2.28/0.68    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 2.28/0.68    inference(cnf_transformation,[],[f25])).
% 2.28/0.68  fof(f25,plain,(
% 2.28/0.68    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.28/0.68    inference(flattening,[],[f24])).
% 2.28/0.68  fof(f24,plain,(
% 2.28/0.68    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.28/0.68    inference(ennf_transformation,[],[f13])).
% 2.28/0.68  fof(f13,axiom,(
% 2.28/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 2.28/0.68  fof(f765,plain,(
% 2.28/0.68    spl2_10),
% 2.28/0.68    inference(avatar_contradiction_clause,[],[f764])).
% 2.28/0.68  fof(f764,plain,(
% 2.28/0.68    $false | spl2_10),
% 2.28/0.68    inference(subsumption_resolution,[],[f763,f35])).
% 2.28/0.68  fof(f763,plain,(
% 2.28/0.68    ~v1_relat_1(k6_relat_1(sK0)) | spl2_10),
% 2.28/0.68    inference(subsumption_resolution,[],[f762,f32])).
% 2.28/0.68  fof(f762,plain,(
% 2.28/0.68    ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(sK0)) | spl2_10),
% 2.28/0.68    inference(resolution,[],[f757,f46])).
% 2.28/0.68  fof(f46,plain,(
% 2.28/0.68    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.28/0.68    inference(cnf_transformation,[],[f27])).
% 2.28/0.68  fof(f27,plain,(
% 2.28/0.68    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.28/0.68    inference(flattening,[],[f26])).
% 2.28/0.68  fof(f26,plain,(
% 2.28/0.68    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.28/0.68    inference(ennf_transformation,[],[f3])).
% 2.28/0.68  fof(f3,axiom,(
% 2.28/0.68    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.28/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.28/0.68  fof(f757,plain,(
% 2.28/0.68    ~v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) | spl2_10),
% 2.28/0.68    inference(avatar_component_clause,[],[f755])).
% 2.28/0.68  % SZS output end Proof for theBenchmark
% 2.28/0.68  % (13478)------------------------------
% 2.28/0.68  % (13478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.68  % (13478)Termination reason: Refutation
% 2.28/0.68  
% 2.28/0.68  % (13478)Memory used [KB]: 12025
% 2.28/0.68  % (13478)Time elapsed: 0.281 s
% 2.28/0.68  % (13478)------------------------------
% 2.28/0.68  % (13478)------------------------------
% 2.28/0.68  % (13455)Success in time 0.324 s
%------------------------------------------------------------------------------
