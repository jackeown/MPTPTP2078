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
% DateTime   : Thu Dec  3 13:07:26 EST 2020

% Result     : Theorem 2.74s
% Output     : Refutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 264 expanded)
%              Number of leaves         :   24 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  277 ( 588 expanded)
%              Number of equality atoms :   77 ( 195 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2757,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f81,f1188,f2170,f2189,f2703])).

fof(f2703,plain,
    ( spl3_7
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f2702])).

fof(f2702,plain,
    ( $false
    | spl3_7
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f2701,f127])).

fof(f127,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_7
  <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f2701,plain,
    ( k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f2640,f149])).

fof(f149,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f148,f59])).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f148,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f55,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f107,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f107,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f55,f59])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2640,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k3_xboole_0(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2))
    | ~ spl3_15 ),
    inference(superposition,[],[f411,f2184])).

fof(f2184,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f2182])).

fof(f2182,plain,
    ( spl3_15
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f411,plain,(
    ! [X2,X3] : k3_xboole_0(X3,X2) = k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f393,f174])).

fof(f174,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k9_relat_1(k6_relat_1(X3),X4) ),
    inference(forward_demodulation,[],[f173,f58])).

fof(f58,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f173,plain,(
    ! [X4,X3] : k9_relat_1(k6_relat_1(X3),X4) = k2_relat_1(k6_relat_1(k3_xboole_0(X3,X4))) ),
    inference(subsumption_resolution,[],[f171,f52])).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f171,plain,(
    ! [X4,X3] :
      ( k9_relat_1(k6_relat_1(X3),X4) = k2_relat_1(k6_relat_1(k3_xboole_0(X3,X4)))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f46,f119])).

fof(f119,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2)) ),
    inference(subsumption_resolution,[],[f117,f52])).

fof(f117,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f54,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f54,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f393,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f387,f149])).

fof(f387,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) ),
    inference(backward_demodulation,[],[f137,f174])).

fof(f137,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) ),
    inference(subsumption_resolution,[],[f136,f52])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f132,f53])).

fof(f53,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f45,f57])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f2189,plain,
    ( spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f2188,f2167,f2182])).

fof(f2167,plain,
    ( spl3_14
  <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f2188,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f2180,f84])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f83,f52])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f50,f57])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f2180,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_14 ),
    inference(resolution,[],[f2169,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f2169,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f2167])).

fof(f2170,plain,
    ( spl3_14
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f2165,f68,f2167])).

fof(f68,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f2165,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f2164,f52])).

fof(f2164,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f2084,f53])).

fof(f2084,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_2 ),
    inference(superposition,[],[f265,f509])).

fof(f509,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(subsumption_resolution,[],[f508,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f508,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,X0)
      | k10_relat_1(k6_relat_1(X0),X0) = X0 ) ),
    inference(forward_demodulation,[],[f507,f57])).

fof(f507,plain,(
    ! [X0] :
      ( k10_relat_1(k6_relat_1(X0),X0) = X0
      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) ) ),
    inference(forward_demodulation,[],[f506,f149])).

fof(f506,plain,(
    ! [X0] :
      ( k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) ) ),
    inference(forward_demodulation,[],[f505,f174])).

fof(f505,plain,(
    ! [X0] :
      ( k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) ) ),
    inference(subsumption_resolution,[],[f504,f52])).

fof(f504,plain,(
    ! [X0] :
      ( k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f502,f53])).

fof(f502,plain,(
    ! [X0] :
      ( k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f157,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f49,f60])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f157,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k10_relat_1(k6_relat_1(X3),X4))
      | k10_relat_1(k6_relat_1(X3),X4) = X3 ) ),
    inference(resolution,[],[f84,f44])).

fof(f265,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f264,f50])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1))
        | ~ r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0)) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1))
        | ~ r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f206,f49])).

fof(f206,plain,
    ( ! [X15] :
        ( r1_tarski(k9_relat_1(X15,k10_relat_1(X15,k10_relat_1(sK0,sK2))),sK1)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
    | ~ spl3_2 ),
    inference(resolution,[],[f133,f102])).

fof(f102,plain,
    ( ! [X7] :
        ( ~ r1_tarski(X7,k10_relat_1(sK0,sK2))
        | r1_tarski(X7,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f48,f70])).

fof(f70,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f51,f45])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1188,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1187,f78,f63,f125])).

fof(f63,plain,
    ( spl3_1
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f78,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1187,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f1186,f80])).

fof(f80,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f1186,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(superposition,[],[f65,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f65,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f71,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f68])).

fof(f39,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f40,f63])).

fof(f40,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 12:17:30 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.53  % (30345)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (30347)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.55  % (30334)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.55  % (30355)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.55  % (30341)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.55  % (30336)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.38/0.55  % (30339)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.38/0.55  % (30362)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.55  % (30335)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.38/0.55  % (30354)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.55  % (30335)Refutation not found, incomplete strategy% (30335)------------------------------
% 1.38/0.55  % (30335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (30335)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (30335)Memory used [KB]: 1663
% 1.38/0.55  % (30335)Time elapsed: 0.124 s
% 1.38/0.55  % (30335)------------------------------
% 1.38/0.55  % (30335)------------------------------
% 1.38/0.56  % (30346)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.56  % (30363)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.56  % (30357)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.38/0.56  % (30337)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.38/0.56  % (30360)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.56  % (30350)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.56  % (30356)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.56  % (30349)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.38/0.56  % (30338)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.38/0.56  % (30361)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.56  % (30351)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.56  % (30340)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.57  % (30359)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.57  % (30343)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.57  % (30352)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.57  % (30342)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.50/0.57  % (30353)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.50/0.57  % (30348)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.50/0.57  % (30344)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.58  % (30358)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.74/0.73  % (30364)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.74/0.75  % (30355)Refutation found. Thanks to Tanya!
% 2.74/0.75  % SZS status Theorem for theBenchmark
% 3.00/0.77  % SZS output start Proof for theBenchmark
% 3.00/0.77  fof(f2757,plain,(
% 3.00/0.77    $false),
% 3.00/0.77    inference(avatar_sat_refutation,[],[f66,f71,f81,f1188,f2170,f2189,f2703])).
% 3.00/0.77  fof(f2703,plain,(
% 3.00/0.77    spl3_7 | ~spl3_15),
% 3.00/0.77    inference(avatar_contradiction_clause,[],[f2702])).
% 3.00/0.77  fof(f2702,plain,(
% 3.00/0.77    $false | (spl3_7 | ~spl3_15)),
% 3.00/0.77    inference(subsumption_resolution,[],[f2701,f127])).
% 3.00/0.77  fof(f127,plain,(
% 3.00/0.77    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | spl3_7),
% 3.00/0.77    inference(avatar_component_clause,[],[f125])).
% 3.00/0.77  fof(f125,plain,(
% 3.00/0.77    spl3_7 <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 3.00/0.77  fof(f2701,plain,(
% 3.00/0.77    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~spl3_15),
% 3.00/0.77    inference(forward_demodulation,[],[f2640,f149])).
% 3.00/0.77  fof(f149,plain,(
% 3.00/0.77    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.00/0.77    inference(forward_demodulation,[],[f148,f59])).
% 3.00/0.77  fof(f59,plain,(
% 3.00/0.77    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.00/0.77    inference(cnf_transformation,[],[f5])).
% 3.00/0.77  fof(f5,axiom,(
% 3.00/0.77    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.00/0.77  fof(f148,plain,(
% 3.00/0.77    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 3.00/0.77    inference(superposition,[],[f55,f109])).
% 3.00/0.77  fof(f109,plain,(
% 3.00/0.77    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.00/0.77    inference(forward_demodulation,[],[f107,f56])).
% 3.00/0.77  fof(f56,plain,(
% 3.00/0.77    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f4])).
% 3.00/0.77  fof(f4,axiom,(
% 3.00/0.77    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 3.00/0.77  fof(f107,plain,(
% 3.00/0.77    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 3.00/0.77    inference(superposition,[],[f55,f59])).
% 3.00/0.77  fof(f55,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.00/0.77    inference(cnf_transformation,[],[f6])).
% 3.00/0.77  fof(f6,axiom,(
% 3.00/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.00/0.77  fof(f2640,plain,(
% 3.00/0.77    k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k3_xboole_0(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) | ~spl3_15),
% 3.00/0.77    inference(superposition,[],[f411,f2184])).
% 3.00/0.77  fof(f2184,plain,(
% 3.00/0.77    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_15),
% 3.00/0.77    inference(avatar_component_clause,[],[f2182])).
% 3.00/0.77  fof(f2182,plain,(
% 3.00/0.77    spl3_15 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 3.00/0.77  fof(f411,plain,(
% 3.00/0.77    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3))) )),
% 3.00/0.77    inference(superposition,[],[f393,f174])).
% 3.00/0.77  fof(f174,plain,(
% 3.00/0.77    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k9_relat_1(k6_relat_1(X3),X4)) )),
% 3.00/0.77    inference(forward_demodulation,[],[f173,f58])).
% 3.00/0.77  fof(f58,plain,(
% 3.00/0.77    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.00/0.77    inference(cnf_transformation,[],[f11])).
% 3.00/0.77  fof(f11,axiom,(
% 3.00/0.77    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.00/0.77  fof(f173,plain,(
% 3.00/0.77    ( ! [X4,X3] : (k9_relat_1(k6_relat_1(X3),X4) = k2_relat_1(k6_relat_1(k3_xboole_0(X3,X4)))) )),
% 3.00/0.77    inference(subsumption_resolution,[],[f171,f52])).
% 3.00/0.77  fof(f52,plain,(
% 3.00/0.77    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.00/0.77    inference(cnf_transformation,[],[f13])).
% 3.00/0.77  fof(f13,axiom,(
% 3.00/0.77    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 3.00/0.77  fof(f171,plain,(
% 3.00/0.77    ( ! [X4,X3] : (k9_relat_1(k6_relat_1(X3),X4) = k2_relat_1(k6_relat_1(k3_xboole_0(X3,X4))) | ~v1_relat_1(k6_relat_1(X3))) )),
% 3.00/0.77    inference(superposition,[],[f46,f119])).
% 3.00/0.77  fof(f119,plain,(
% 3.00/0.77    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2))) )),
% 3.00/0.77    inference(subsumption_resolution,[],[f117,f52])).
% 3.00/0.77  fof(f117,plain,(
% 3.00/0.77    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 3.00/0.77    inference(superposition,[],[f54,f47])).
% 3.00/0.77  fof(f47,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f26])).
% 3.00/0.77  fof(f26,plain,(
% 3.00/0.77    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.00/0.77    inference(ennf_transformation,[],[f12])).
% 3.00/0.77  fof(f12,axiom,(
% 3.00/0.77    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 3.00/0.77  fof(f54,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 3.00/0.77    inference(cnf_transformation,[],[f17])).
% 3.00/0.77  fof(f17,axiom,(
% 3.00/0.77    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 3.00/0.77  fof(f46,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f25])).
% 3.00/0.77  fof(f25,plain,(
% 3.00/0.77    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.00/0.77    inference(ennf_transformation,[],[f9])).
% 3.00/0.77  fof(f9,axiom,(
% 3.00/0.77    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 3.00/0.77  fof(f393,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1))) )),
% 3.00/0.77    inference(forward_demodulation,[],[f387,f149])).
% 3.00/0.77  fof(f387,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0))) )),
% 3.00/0.77    inference(backward_demodulation,[],[f137,f174])).
% 3.00/0.77  fof(f137,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))) )),
% 3.00/0.77    inference(subsumption_resolution,[],[f136,f52])).
% 3.00/0.77  fof(f136,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.00/0.77    inference(subsumption_resolution,[],[f132,f53])).
% 3.00/0.77  fof(f53,plain,(
% 3.00/0.77    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.00/0.77    inference(cnf_transformation,[],[f13])).
% 3.00/0.77  fof(f132,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.00/0.77    inference(superposition,[],[f45,f57])).
% 3.00/0.77  fof(f57,plain,(
% 3.00/0.77    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.00/0.77    inference(cnf_transformation,[],[f11])).
% 3.00/0.77  fof(f45,plain,(
% 3.00/0.77    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f24])).
% 3.00/0.77  fof(f24,plain,(
% 3.00/0.77    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.00/0.77    inference(flattening,[],[f23])).
% 3.00/0.77  fof(f23,plain,(
% 3.00/0.77    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.00/0.77    inference(ennf_transformation,[],[f15])).
% 3.00/0.77  fof(f15,axiom,(
% 3.00/0.77    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 3.00/0.77  fof(f2189,plain,(
% 3.00/0.77    spl3_15 | ~spl3_14),
% 3.00/0.77    inference(avatar_split_clause,[],[f2188,f2167,f2182])).
% 3.00/0.77  fof(f2167,plain,(
% 3.00/0.77    spl3_14 <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 3.00/0.77  fof(f2188,plain,(
% 3.00/0.77    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_14),
% 3.00/0.77    inference(subsumption_resolution,[],[f2180,f84])).
% 3.00/0.77  fof(f84,plain,(
% 3.00/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 3.00/0.77    inference(subsumption_resolution,[],[f83,f52])).
% 3.00/0.77  fof(f83,plain,(
% 3.00/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.00/0.77    inference(superposition,[],[f50,f57])).
% 3.00/0.77  fof(f50,plain,(
% 3.00/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f31])).
% 3.00/0.77  fof(f31,plain,(
% 3.00/0.77    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.00/0.77    inference(ennf_transformation,[],[f10])).
% 3.00/0.77  fof(f10,axiom,(
% 3.00/0.77    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 3.00/0.77  fof(f2180,plain,(
% 3.00/0.77    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) | ~spl3_14),
% 3.00/0.77    inference(resolution,[],[f2169,f44])).
% 3.00/0.77  fof(f44,plain,(
% 3.00/0.77    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f36])).
% 3.00/0.77  fof(f36,plain,(
% 3.00/0.77    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/0.77    inference(flattening,[],[f35])).
% 3.00/0.77  fof(f35,plain,(
% 3.00/0.77    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/0.77    inference(nnf_transformation,[],[f1])).
% 3.00/0.77  fof(f1,axiom,(
% 3.00/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.00/0.77  fof(f2169,plain,(
% 3.00/0.77    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_14),
% 3.00/0.77    inference(avatar_component_clause,[],[f2167])).
% 3.00/0.77  fof(f2170,plain,(
% 3.00/0.77    spl3_14 | ~spl3_2),
% 3.00/0.77    inference(avatar_split_clause,[],[f2165,f68,f2167])).
% 3.00/0.77  fof(f68,plain,(
% 3.00/0.77    spl3_2 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.00/0.77  fof(f2165,plain,(
% 3.00/0.77    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_2),
% 3.00/0.77    inference(subsumption_resolution,[],[f2164,f52])).
% 3.00/0.77  fof(f2164,plain,(
% 3.00/0.77    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_2),
% 3.00/0.77    inference(subsumption_resolution,[],[f2084,f53])).
% 3.00/0.77  fof(f2084,plain,(
% 3.00/0.77    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_2),
% 3.00/0.77    inference(superposition,[],[f265,f509])).
% 3.00/0.77  fof(f509,plain,(
% 3.00/0.77    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 3.00/0.77    inference(subsumption_resolution,[],[f508,f60])).
% 3.00/0.77  fof(f60,plain,(
% 3.00/0.77    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.00/0.77    inference(equality_resolution,[],[f43])).
% 3.00/0.77  fof(f43,plain,(
% 3.00/0.77    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.00/0.77    inference(cnf_transformation,[],[f36])).
% 3.00/0.77  fof(f508,plain,(
% 3.00/0.77    ( ! [X0] : (~r1_tarski(X0,X0) | k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 3.00/0.77    inference(forward_demodulation,[],[f507,f57])).
% 3.00/0.77  fof(f507,plain,(
% 3.00/0.77    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0 | ~r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))) )),
% 3.00/0.77    inference(forward_demodulation,[],[f506,f149])).
% 3.00/0.77  fof(f506,plain,(
% 3.00/0.77    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))) )),
% 3.00/0.77    inference(forward_demodulation,[],[f505,f174])).
% 3.00/0.77  fof(f505,plain,(
% 3.00/0.77    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X0)) = X0 | ~r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))) )),
% 3.00/0.77    inference(subsumption_resolution,[],[f504,f52])).
% 3.00/0.77  fof(f504,plain,(
% 3.00/0.77    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X0)) = X0 | ~r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.00/0.77    inference(subsumption_resolution,[],[f502,f53])).
% 3.00/0.77  fof(f502,plain,(
% 3.00/0.77    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X0)) = X0 | ~r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.00/0.77    inference(resolution,[],[f157,f142])).
% 3.00/0.77  fof(f142,plain,(
% 3.00/0.77    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.00/0.77    inference(resolution,[],[f49,f60])).
% 3.00/0.77  fof(f49,plain,(
% 3.00/0.77    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f30])).
% 3.00/0.77  fof(f30,plain,(
% 3.00/0.77    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.00/0.77    inference(flattening,[],[f29])).
% 3.00/0.77  fof(f29,plain,(
% 3.00/0.77    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.00/0.77    inference(ennf_transformation,[],[f16])).
% 3.00/0.77  fof(f16,axiom,(
% 3.00/0.77    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 3.00/0.77  fof(f157,plain,(
% 3.00/0.77    ( ! [X4,X3] : (~r1_tarski(X3,k10_relat_1(k6_relat_1(X3),X4)) | k10_relat_1(k6_relat_1(X3),X4) = X3) )),
% 3.00/0.77    inference(resolution,[],[f84,f44])).
% 3.00/0.77  fof(f265,plain,(
% 3.00/0.77    ( ! [X0] : (r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_2),
% 3.00/0.77    inference(subsumption_resolution,[],[f264,f50])).
% 3.00/0.77  fof(f264,plain,(
% 3.00/0.77    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1)) | ~r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0))) ) | ~spl3_2),
% 3.00/0.77    inference(duplicate_literal_removal,[],[f259])).
% 3.00/0.77  fof(f259,plain,(
% 3.00/0.77    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1)) | ~r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_2),
% 3.00/0.77    inference(resolution,[],[f206,f49])).
% 3.00/0.77  fof(f206,plain,(
% 3.00/0.77    ( ! [X15] : (r1_tarski(k9_relat_1(X15,k10_relat_1(X15,k10_relat_1(sK0,sK2))),sK1) | ~v1_relat_1(X15) | ~v1_funct_1(X15)) ) | ~spl3_2),
% 3.00/0.77    inference(resolution,[],[f133,f102])).
% 3.00/0.77  fof(f102,plain,(
% 3.00/0.77    ( ! [X7] : (~r1_tarski(X7,k10_relat_1(sK0,sK2)) | r1_tarski(X7,sK1)) ) | ~spl3_2),
% 3.00/0.77    inference(resolution,[],[f48,f70])).
% 3.00/0.77  fof(f70,plain,(
% 3.00/0.77    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_2),
% 3.00/0.77    inference(avatar_component_clause,[],[f68])).
% 3.00/0.77  fof(f48,plain,(
% 3.00/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f28])).
% 3.00/0.77  fof(f28,plain,(
% 3.00/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.00/0.77    inference(flattening,[],[f27])).
% 3.00/0.77  fof(f27,plain,(
% 3.00/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.00/0.77    inference(ennf_transformation,[],[f3])).
% 3.00/0.77  fof(f3,axiom,(
% 3.00/0.77    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.00/0.77  fof(f133,plain,(
% 3.00/0.77    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.00/0.77    inference(superposition,[],[f51,f45])).
% 3.00/0.77  fof(f51,plain,(
% 3.00/0.77    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f2])).
% 3.00/0.77  fof(f2,axiom,(
% 3.00/0.77    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.00/0.77  fof(f1188,plain,(
% 3.00/0.77    ~spl3_7 | spl3_1 | ~spl3_4),
% 3.00/0.77    inference(avatar_split_clause,[],[f1187,f78,f63,f125])).
% 3.00/0.77  fof(f63,plain,(
% 3.00/0.77    spl3_1 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.00/0.77  fof(f78,plain,(
% 3.00/0.77    spl3_4 <=> v1_relat_1(sK0)),
% 3.00/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 3.00/0.77  fof(f1187,plain,(
% 3.00/0.77    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | (spl3_1 | ~spl3_4)),
% 3.00/0.77    inference(subsumption_resolution,[],[f1186,f80])).
% 3.00/0.77  fof(f80,plain,(
% 3.00/0.77    v1_relat_1(sK0) | ~spl3_4),
% 3.00/0.77    inference(avatar_component_clause,[],[f78])).
% 3.00/0.77  fof(f1186,plain,(
% 3.00/0.77    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | spl3_1),
% 3.00/0.77    inference(superposition,[],[f65,f41])).
% 3.00/0.77  fof(f41,plain,(
% 3.00/0.77    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.00/0.77    inference(cnf_transformation,[],[f22])).
% 3.00/0.77  fof(f22,plain,(
% 3.00/0.77    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.00/0.77    inference(ennf_transformation,[],[f14])).
% 3.00/0.77  fof(f14,axiom,(
% 3.00/0.77    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 3.00/0.77  fof(f65,plain,(
% 3.00/0.77    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_1),
% 3.00/0.77    inference(avatar_component_clause,[],[f63])).
% 3.00/0.77  fof(f81,plain,(
% 3.00/0.77    spl3_4),
% 3.00/0.77    inference(avatar_split_clause,[],[f37,f78])).
% 3.00/0.77  fof(f37,plain,(
% 3.00/0.77    v1_relat_1(sK0)),
% 3.00/0.77    inference(cnf_transformation,[],[f34])).
% 3.00/0.77  fof(f34,plain,(
% 3.00/0.77    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 3.00/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f33,f32])).
% 3.00/0.77  fof(f32,plain,(
% 3.00/0.77    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 3.00/0.77    introduced(choice_axiom,[])).
% 3.00/0.77  fof(f33,plain,(
% 3.00/0.77    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 3.00/0.77    introduced(choice_axiom,[])).
% 3.00/0.77  fof(f21,plain,(
% 3.00/0.77    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.00/0.77    inference(flattening,[],[f20])).
% 3.00/0.77  fof(f20,plain,(
% 3.00/0.77    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.00/0.77    inference(ennf_transformation,[],[f19])).
% 3.00/0.77  fof(f19,negated_conjecture,(
% 3.00/0.77    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.00/0.77    inference(negated_conjecture,[],[f18])).
% 3.00/0.77  fof(f18,conjecture,(
% 3.00/0.77    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.00/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 3.00/0.77  fof(f71,plain,(
% 3.00/0.77    spl3_2),
% 3.00/0.77    inference(avatar_split_clause,[],[f39,f68])).
% 3.00/0.77  fof(f39,plain,(
% 3.00/0.77    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 3.00/0.77    inference(cnf_transformation,[],[f34])).
% 3.00/0.77  fof(f66,plain,(
% 3.00/0.77    ~spl3_1),
% 3.00/0.77    inference(avatar_split_clause,[],[f40,f63])).
% 3.00/0.77  fof(f40,plain,(
% 3.00/0.77    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 3.00/0.77    inference(cnf_transformation,[],[f34])).
% 3.00/0.77  % SZS output end Proof for theBenchmark
% 3.00/0.77  % (30355)------------------------------
% 3.00/0.77  % (30355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.00/0.77  % (30355)Termination reason: Refutation
% 3.00/0.77  
% 3.00/0.77  % (30355)Memory used [KB]: 7931
% 3.00/0.77  % (30355)Time elapsed: 0.320 s
% 3.00/0.77  % (30355)------------------------------
% 3.00/0.77  % (30355)------------------------------
% 3.00/0.77  % (30333)Success in time 0.394 s
%------------------------------------------------------------------------------
