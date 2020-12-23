%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0678+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 211 expanded)
%              Number of leaves         :   11 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 671 expanded)
%              Number of equality atoms :   52 ( 185 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f416,plain,(
    $false ),
    inference(subsumption_resolution,[],[f407,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f32,f48])).

fof(f48,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unit_resulting_resolution,[],[f32,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f407,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f130,f399])).

fof(f399,plain,(
    k1_xboole_0 = k11_relat_1(sK0,sK1(sK0)) ),
    inference(superposition,[],[f365,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f365,plain,(
    k1_xboole_0 = k3_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0))) ),
    inference(forward_demodulation,[],[f364,f51])).

fof(f51,plain,(
    k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

% (26025)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_funct_1)).

fof(f364,plain,(
    k9_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK1(sK0))) ),
    inference(forward_demodulation,[],[f341,f126])).

fof(f126,plain,(
    k11_relat_1(sK0,sK1(sK0)) = k11_relat_1(sK0,sK2(sK0)) ),
    inference(backward_demodulation,[],[f125,f123])).

fof(f123,plain,(
    k11_relat_1(sK0,sK1(sK0)) = k1_tarski(k1_funct_1(sK0,sK1(sK0))) ),
    inference(unit_resulting_resolution,[],[f29,f28,f61,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f61,plain,(
    r2_hidden(sK1(sK0),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f31,f28,f29,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f31,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f29,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f125,plain,(
    k1_tarski(k1_funct_1(sK0,sK1(sK0))) = k11_relat_1(sK0,sK2(sK0)) ),
    inference(forward_demodulation,[],[f124,f86])).

fof(f86,plain,(
    k1_funct_1(sK0,sK1(sK0)) = k1_funct_1(sK0,sK2(sK0)) ),
    inference(unit_resulting_resolution,[],[f28,f31,f29,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK2(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f124,plain,(
    k11_relat_1(sK0,sK2(sK0)) = k1_tarski(k1_funct_1(sK0,sK2(sK0))) ),
    inference(unit_resulting_resolution,[],[f29,f28,f62,f46])).

fof(f62,plain,(
    r2_hidden(sK2(sK0),k1_relat_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f31,f28,f29,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f341,plain,(
    k9_relat_1(sK0,k1_xboole_0) = k3_xboole_0(k11_relat_1(sK0,sK1(sK0)),k11_relat_1(sK0,sK2(sK0))) ),
    inference(superposition,[],[f147,f66])).

fof(f66,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0))) ),
    inference(unit_resulting_resolution,[],[f64,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f64,plain,(
    r1_xboole_0(k1_tarski(sK1(sK0)),k1_tarski(sK2(sK0))) ),
    inference(unit_resulting_resolution,[],[f63,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f63,plain,(
    sK1(sK0) != sK2(sK0) ),
    inference(unit_resulting_resolution,[],[f31,f28,f29,f42])).

fof(f42,plain,(
    ! [X0] :
      ( sK1(X0) != sK2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f147,plain,(
    ! [X8,X7] : k9_relat_1(sK0,k3_xboole_0(k1_tarski(X8),k1_tarski(X7))) = k3_xboole_0(k11_relat_1(sK0,X8),k11_relat_1(sK0,X7)) ),
    inference(superposition,[],[f68,f60])).

fof(f60,plain,(
    ! [X0] : k11_relat_1(sK0,X0) = k9_relat_1(sK0,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f68,plain,(
    ! [X2,X1] : k9_relat_1(sK0,k3_xboole_0(k1_tarski(X1),X2)) = k3_xboole_0(k11_relat_1(sK0,X1),k9_relat_1(sK0,X2)) ),
    inference(superposition,[],[f30,f60])).

fof(f30,plain,(
    ! [X2,X1] : k9_relat_1(sK0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(sK0,X1),k9_relat_1(sK0,X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f130,plain,(
    ~ v1_xboole_0(k11_relat_1(sK0,sK1(sK0))) ),
    inference(superposition,[],[f33,f123])).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

%------------------------------------------------------------------------------
