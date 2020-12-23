%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0702+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:45 EST 2020

% Result     : Theorem 41.34s
% Output     : Refutation 41.34s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 164 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  169 ( 642 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42670,plain,(
    $false ),
    inference(subsumption_resolution,[],[f42546,f17735])).

fof(f17735,plain,(
    ! [X15] : ~ r1_tarski(sK0,k3_xboole_0(X15,sK1)) ),
    inference(superposition,[],[f4356,f2260])).

fof(f2260,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f4356,plain,(
    ! [X2] : ~ r1_tarski(sK0,k3_xboole_0(sK1,X2)) ),
    inference(resolution,[],[f1704,f1901])).

fof(f1901,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1196])).

fof(f1196,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f74])).

fof(f74,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f1704,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f1024])).

fof(f1024,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1023])).

fof(f1023,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f959])).

fof(f959,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f958])).

fof(f958,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f42546,plain,(
    r1_tarski(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(backward_demodulation,[],[f40367,f42355])).

fof(f42355,plain,(
    ! [X89] : k3_xboole_0(k1_relat_1(sK2),X89) = k10_relat_1(sK2,k9_relat_1(sK2,X89)) ),
    inference(subsumption_resolution,[],[f42241,f23893])).

fof(f23893,plain,(
    ! [X13] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X13)),k3_xboole_0(k1_relat_1(sK2),X13)) ),
    inference(subsumption_resolution,[],[f23870,f1699])).

fof(f1699,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1024])).

fof(f23870,plain,(
    ! [X13] :
      ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X13)),k3_xboole_0(k1_relat_1(sK2),X13))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f3437,f1840])).

fof(f1840,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f1135])).

fof(f1135,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f747])).

fof(f747,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f3437,plain,(
    ! [X12] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X12)),X12) ),
    inference(subsumption_resolution,[],[f3436,f1703])).

fof(f1703,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1024])).

fof(f3436,plain,(
    ! [X12] :
      ( ~ v2_funct_1(sK2)
      | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X12)),X12) ) ),
    inference(subsumption_resolution,[],[f2887,f1700])).

fof(f1700,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1024])).

fof(f2887,plain,(
    ! [X12] :
      ( ~ v1_funct_1(sK2)
      | ~ v2_funct_1(sK2)
      | r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X12)),X12) ) ),
    inference(resolution,[],[f1699,f1718])).

fof(f1718,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f1042])).

fof(f1042,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1041])).

fof(f1041,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f953])).

fof(f953,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f42241,plain,(
    ! [X89] :
      ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X89)),k3_xboole_0(k1_relat_1(sK2),X89))
      | k3_xboole_0(k1_relat_1(sK2),X89) = k10_relat_1(sK2,k9_relat_1(sK2,X89)) ) ),
    inference(resolution,[],[f3589,f1940])).

fof(f1940,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3589,plain,(
    ! [X196] : r1_tarski(k3_xboole_0(k1_relat_1(sK2),X196),k10_relat_1(sK2,k9_relat_1(sK2,X196))) ),
    inference(forward_demodulation,[],[f3070,f3524])).

fof(f3524,plain,(
    ! [X11] : k10_relat_1(sK2,X11) = k9_relat_1(k4_relat_1(sK2),X11) ),
    inference(backward_demodulation,[],[f3435,f3520])).

fof(f3520,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f3519,f1703])).

fof(f3519,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f2958,f1700])).

fof(f2958,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f1699,f1778])).

fof(f1778,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f1092])).

fof(f1092,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1091])).

fof(f1091,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f896])).

fof(f896,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f3435,plain,(
    ! [X11] : k10_relat_1(sK2,X11) = k9_relat_1(k2_funct_1(sK2),X11) ),
    inference(subsumption_resolution,[],[f3434,f1703])).

fof(f3434,plain,(
    ! [X11] :
      ( ~ v2_funct_1(sK2)
      | k10_relat_1(sK2,X11) = k9_relat_1(k2_funct_1(sK2),X11) ) ),
    inference(subsumption_resolution,[],[f2886,f1700])).

fof(f2886,plain,(
    ! [X11] :
      ( ~ v1_funct_1(sK2)
      | ~ v2_funct_1(sK2)
      | k10_relat_1(sK2,X11) = k9_relat_1(k2_funct_1(sK2),X11) ) ),
    inference(resolution,[],[f1699,f1717])).

fof(f1717,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f1040])).

fof(f1040,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1039])).

fof(f1039,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f956])).

fof(f956,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f3070,plain,(
    ! [X196] : r1_tarski(k3_xboole_0(k1_relat_1(sK2),X196),k9_relat_1(k4_relat_1(sK2),k9_relat_1(sK2,X196))) ),
    inference(resolution,[],[f1699,f1983])).

fof(f1983,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f1258])).

fof(f1258,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f767])).

fof(f767,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).

fof(f40367,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    inference(forward_demodulation,[],[f40296,f24833])).

fof(f24833,plain,(
    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f24761,f3437])).

fof(f24761,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)
    | sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f4487,f1940])).

fof(f4487,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(subsumption_resolution,[],[f4379,f1699])).

fof(f4379,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(resolution,[],[f1702,f1982])).

fof(f1982,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f1257])).

fof(f1257,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1256])).

fof(f1256,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f946])).

fof(f946,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f1702,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f1024])).

fof(f40296,plain,(
    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k10_relat_1(sK2,k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f3296,f1701])).

fof(f1701,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f1024])).

fof(f3296,plain,(
    ! [X563,X564] :
      ( ~ r1_tarski(X563,X564)
      | r1_tarski(k10_relat_1(sK2,X563),k10_relat_1(sK2,X564)) ) ),
    inference(resolution,[],[f1699,f2458])).

fof(f2458,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f1556])).

fof(f1556,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1555])).

fof(f1555,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f780])).

fof(f780,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
%------------------------------------------------------------------------------
