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
% DateTime   : Thu Dec  3 13:07:24 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 151 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  243 ( 380 expanded)
%              Number of equality atoms :   54 (  95 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f428,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f82,f138,f181,f232,f257,f427])).

fof(f427,plain,
    ( spl3_7
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | spl3_7
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f399,f137])).

fof(f137,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_7
  <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f399,plain,
    ( k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ spl3_12 ),
    inference(superposition,[],[f256,f220])).

fof(f220,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0) ),
    inference(forward_demodulation,[],[f219,f58])).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f219,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(subsumption_resolution,[],[f212,f54])).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f212,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f149,f56])).

fof(f56,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f149,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f139,f54])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f52,f58])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f256,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl3_12
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f257,plain,
    ( spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f252,f229,f254])).

fof(f229,plain,
    ( spl3_9
  <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f252,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f251,f91])).

fof(f91,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f90,f54])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f51,f58])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f251,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f231,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f231,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f229])).

fof(f232,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f227,f178,f229])).

fof(f178,plain,
    ( spl3_8
  <=> r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f227,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f226,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f226,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2))
    | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f225,f58])).

fof(f225,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f224,f54])).

fof(f224,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f221,f55])).

fof(f55,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f221,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_8 ),
    inference(resolution,[],[f180,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f180,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f178])).

fof(f181,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f176,f69,f178])).

fof(f69,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f176,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f164,f127])).

fof(f127,plain,(
    ! [X1] : r1_tarski(k9_relat_1(k6_relat_1(X1),X1),X1) ),
    inference(subsumption_resolution,[],[f126,f54])).

fof(f126,plain,(
    ! [X1] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X1),X1),X1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f124,f55])).

fof(f124,plain,(
    ! [X1] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X1),X1),X1)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f49,f115])).

fof(f115,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f114,f58])).

fof(f114,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f110,f54])).

fof(f110,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f53,f59])).

fof(f59,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k10_relat_1(sK0,sK2))
        | r1_tarski(X0,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f86,f71])).

fof(f71,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f86,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X4)
      | r1_tarski(X2,X4)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f48,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f138,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f133,f79,f64,f135])).

fof(f64,plain,
    ( spl3_1
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f133,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f132,f81])).

fof(f81,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f132,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(superposition,[],[f66,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f66,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f82,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f79])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f72,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f41,f69])).

fof(f41,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f42,f64])).

fof(f42,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (31486)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (31477)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (31469)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (31468)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (31464)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (31465)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.54  % (31464)Refutation not found, incomplete strategy% (31464)------------------------------
% 0.20/0.54  % (31464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31464)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31464)Memory used [KB]: 1663
% 0.20/0.54  % (31464)Time elapsed: 0.121 s
% 0.20/0.54  % (31464)------------------------------
% 0.20/0.54  % (31464)------------------------------
% 0.20/0.54  % (31491)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.54  % (31467)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.42/0.54  % (31489)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.42/0.55  % (31475)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.42/0.55  % (31463)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.42/0.55  % (31482)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.55  % (31475)Refutation not found, incomplete strategy% (31475)------------------------------
% 1.42/0.55  % (31475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (31475)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (31475)Memory used [KB]: 10618
% 1.42/0.55  % (31475)Time elapsed: 0.132 s
% 1.42/0.55  % (31475)------------------------------
% 1.42/0.55  % (31475)------------------------------
% 1.42/0.55  % (31476)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.42/0.55  % (31480)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.55  % (31492)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.42/0.55  % (31485)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.55  % (31474)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.55  % (31470)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.42/0.55  % (31472)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.55  % (31484)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.55  % (31466)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.42/0.56  % (31493)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.56  % (31487)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.42/0.56  % (31493)Refutation not found, incomplete strategy% (31493)------------------------------
% 1.42/0.56  % (31493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (31493)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (31493)Memory used [KB]: 1663
% 1.42/0.56  % (31493)Time elapsed: 0.144 s
% 1.42/0.56  % (31493)------------------------------
% 1.42/0.56  % (31493)------------------------------
% 1.42/0.56  % (31481)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.56  % (31490)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.60/0.56  % (31473)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.60/0.56  % (31490)Refutation not found, incomplete strategy% (31490)------------------------------
% 1.60/0.56  % (31490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (31492)Refutation not found, incomplete strategy% (31492)------------------------------
% 1.60/0.57  % (31492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (31481)Refutation not found, incomplete strategy% (31481)------------------------------
% 1.60/0.57  % (31481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (31478)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.60/0.57  % (31473)Refutation not found, incomplete strategy% (31473)------------------------------
% 1.60/0.57  % (31473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (31490)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (31490)Memory used [KB]: 6268
% 1.60/0.57  % (31490)Time elapsed: 0.157 s
% 1.60/0.57  % (31490)------------------------------
% 1.60/0.57  % (31490)------------------------------
% 1.60/0.57  % (31492)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (31492)Memory used [KB]: 10746
% 1.60/0.57  % (31492)Time elapsed: 0.160 s
% 1.60/0.57  % (31492)------------------------------
% 1.60/0.57  % (31492)------------------------------
% 1.60/0.58  % (31481)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (31481)Memory used [KB]: 1791
% 1.60/0.58  % (31481)Time elapsed: 0.157 s
% 1.60/0.58  % (31481)------------------------------
% 1.60/0.58  % (31481)------------------------------
% 1.60/0.58  % (31473)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (31473)Memory used [KB]: 10746
% 1.60/0.58  % (31473)Time elapsed: 0.152 s
% 1.60/0.58  % (31473)------------------------------
% 1.60/0.58  % (31473)------------------------------
% 1.60/0.58  % (31485)Refutation found. Thanks to Tanya!
% 1.60/0.58  % SZS status Theorem for theBenchmark
% 1.60/0.58  % SZS output start Proof for theBenchmark
% 1.60/0.58  fof(f428,plain,(
% 1.60/0.58    $false),
% 1.60/0.58    inference(avatar_sat_refutation,[],[f67,f72,f82,f138,f181,f232,f257,f427])).
% 1.60/0.58  fof(f427,plain,(
% 1.60/0.58    spl3_7 | ~spl3_12),
% 1.60/0.58    inference(avatar_contradiction_clause,[],[f426])).
% 1.60/0.58  fof(f426,plain,(
% 1.60/0.58    $false | (spl3_7 | ~spl3_12)),
% 1.60/0.58    inference(subsumption_resolution,[],[f399,f137])).
% 1.60/0.58  fof(f137,plain,(
% 1.60/0.58    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | spl3_7),
% 1.60/0.58    inference(avatar_component_clause,[],[f135])).
% 1.60/0.58  fof(f135,plain,(
% 1.60/0.58    spl3_7 <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.60/0.58  fof(f399,plain,(
% 1.60/0.58    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~spl3_12),
% 1.60/0.58    inference(superposition,[],[f256,f220])).
% 1.60/0.58  fof(f220,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0)) )),
% 1.60/0.58    inference(forward_demodulation,[],[f219,f58])).
% 1.60/0.58  fof(f58,plain,(
% 1.60/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f14])).
% 1.60/0.58  fof(f14,axiom,(
% 1.60/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.60/0.58  fof(f219,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f212,f54])).
% 1.60/0.58  fof(f54,plain,(
% 1.60/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f15])).
% 1.60/0.58  fof(f15,axiom,(
% 1.60/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.60/0.58  fof(f212,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.60/0.58    inference(superposition,[],[f149,f56])).
% 1.60/0.58  fof(f56,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f19])).
% 1.60/0.58  fof(f19,axiom,(
% 1.60/0.58    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.60/0.58  fof(f149,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) | ~v1_relat_1(X1)) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f139,f54])).
% 1.60/0.58  fof(f139,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.60/0.58    inference(superposition,[],[f52,f58])).
% 1.60/0.58  fof(f52,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f32])).
% 1.60/0.58  fof(f32,plain,(
% 1.60/0.58    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f13])).
% 1.60/0.58  fof(f13,axiom,(
% 1.60/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.60/0.58  fof(f256,plain,(
% 1.60/0.58    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_12),
% 1.60/0.58    inference(avatar_component_clause,[],[f254])).
% 1.60/0.58  fof(f254,plain,(
% 1.60/0.58    spl3_12 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.60/0.58  fof(f257,plain,(
% 1.60/0.58    spl3_12 | ~spl3_9),
% 1.60/0.58    inference(avatar_split_clause,[],[f252,f229,f254])).
% 1.60/0.58  fof(f229,plain,(
% 1.60/0.58    spl3_9 <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.60/0.58  fof(f252,plain,(
% 1.60/0.58    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_9),
% 1.60/0.58    inference(subsumption_resolution,[],[f251,f91])).
% 1.60/0.58  fof(f91,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f90,f54])).
% 1.60/0.58  fof(f90,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.60/0.58    inference(superposition,[],[f51,f58])).
% 1.60/0.58  fof(f51,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f31])).
% 1.60/0.58  fof(f31,plain,(
% 1.60/0.58    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f11])).
% 1.60/0.58  fof(f11,axiom,(
% 1.60/0.58    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.60/0.58  fof(f251,plain,(
% 1.60/0.58    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) | ~spl3_9),
% 1.60/0.58    inference(resolution,[],[f231,f45])).
% 1.60/0.58  fof(f45,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f38])).
% 1.60/0.58  fof(f38,plain,(
% 1.60/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.58    inference(flattening,[],[f37])).
% 1.60/0.58  fof(f37,plain,(
% 1.60/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.58    inference(nnf_transformation,[],[f1])).
% 1.60/0.58  fof(f1,axiom,(
% 1.60/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.58  fof(f231,plain,(
% 1.60/0.58    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_9),
% 1.60/0.58    inference(avatar_component_clause,[],[f229])).
% 1.60/0.58  fof(f232,plain,(
% 1.60/0.58    spl3_9 | ~spl3_8),
% 1.60/0.58    inference(avatar_split_clause,[],[f227,f178,f229])).
% 1.60/0.58  fof(f178,plain,(
% 1.60/0.58    spl3_8 <=> r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.60/0.58  fof(f227,plain,(
% 1.60/0.58    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_8),
% 1.60/0.58    inference(subsumption_resolution,[],[f226,f61])).
% 1.60/0.58  fof(f61,plain,(
% 1.60/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.58    inference(equality_resolution,[],[f44])).
% 1.60/0.58  fof(f44,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.60/0.58    inference(cnf_transformation,[],[f38])).
% 1.60/0.58  fof(f226,plain,(
% 1.60/0.58    ~r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_8),
% 1.60/0.58    inference(forward_demodulation,[],[f225,f58])).
% 1.60/0.58  fof(f225,plain,(
% 1.60/0.58    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~spl3_8),
% 1.60/0.58    inference(subsumption_resolution,[],[f224,f54])).
% 1.60/0.58  fof(f224,plain,(
% 1.60/0.58    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_8),
% 1.60/0.58    inference(subsumption_resolution,[],[f221,f55])).
% 1.60/0.58  fof(f55,plain,(
% 1.60/0.58    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f15])).
% 1.60/0.58  fof(f221,plain,(
% 1.60/0.58    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_8),
% 1.60/0.58    inference(resolution,[],[f180,f47])).
% 1.60/0.58  fof(f47,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f26])).
% 1.60/0.58  fof(f26,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.60/0.58    inference(flattening,[],[f25])).
% 1.60/0.58  fof(f25,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.60/0.58    inference(ennf_transformation,[],[f18])).
% 1.60/0.58  fof(f18,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.60/0.58  fof(f180,plain,(
% 1.60/0.58    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) | ~spl3_8),
% 1.60/0.58    inference(avatar_component_clause,[],[f178])).
% 1.60/0.58  fof(f181,plain,(
% 1.60/0.58    spl3_8 | ~spl3_2),
% 1.60/0.58    inference(avatar_split_clause,[],[f176,f69,f178])).
% 1.60/0.58  fof(f69,plain,(
% 1.60/0.58    spl3_2 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.60/0.58  fof(f176,plain,(
% 1.60/0.58    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) | ~spl3_2),
% 1.60/0.58    inference(resolution,[],[f164,f127])).
% 1.60/0.58  fof(f127,plain,(
% 1.60/0.58    ( ! [X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),X1),X1)) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f126,f54])).
% 1.60/0.58  fof(f126,plain,(
% 1.60/0.58    ( ! [X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),X1),X1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f124,f55])).
% 1.60/0.58  fof(f124,plain,(
% 1.60/0.58    ( ! [X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),X1),X1) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.60/0.58    inference(superposition,[],[f49,f115])).
% 1.60/0.58  fof(f115,plain,(
% 1.60/0.58    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.60/0.58    inference(forward_demodulation,[],[f114,f58])).
% 1.60/0.58  fof(f114,plain,(
% 1.60/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f110,f54])).
% 1.60/0.58  fof(f110,plain,(
% 1.60/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.60/0.58    inference(superposition,[],[f53,f59])).
% 1.60/0.58  fof(f59,plain,(
% 1.60/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f14])).
% 1.60/0.58  fof(f53,plain,(
% 1.60/0.58    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f33])).
% 1.60/0.58  fof(f33,plain,(
% 1.60/0.58    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.58    inference(ennf_transformation,[],[f12])).
% 1.60/0.58  fof(f12,axiom,(
% 1.60/0.58    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.60/0.58  fof(f49,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f29])).
% 1.60/0.58  fof(f29,plain,(
% 1.60/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.60/0.58    inference(flattening,[],[f28])).
% 1.60/0.58  fof(f28,plain,(
% 1.60/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.60/0.58    inference(ennf_transformation,[],[f17])).
% 1.60/0.58  fof(f17,axiom,(
% 1.60/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.60/0.58  fof(f164,plain,(
% 1.60/0.58    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK0,sK2)) | r1_tarski(X0,sK1)) ) | ~spl3_2),
% 1.60/0.58    inference(resolution,[],[f86,f71])).
% 1.60/0.58  fof(f71,plain,(
% 1.60/0.58    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_2),
% 1.60/0.58    inference(avatar_component_clause,[],[f69])).
% 1.60/0.58  fof(f86,plain,(
% 1.60/0.58    ( ! [X4,X2,X3] : (~r1_tarski(X3,X4) | r1_tarski(X2,X4) | ~r1_tarski(X2,X3)) )),
% 1.60/0.58    inference(superposition,[],[f48,f50])).
% 1.60/0.58  fof(f50,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f30])).
% 1.60/0.58  fof(f30,plain,(
% 1.60/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f3])).
% 1.60/0.58  fof(f3,axiom,(
% 1.60/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.60/0.58  fof(f48,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f27])).
% 1.60/0.58  fof(f27,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.60/0.58    inference(ennf_transformation,[],[f2])).
% 1.60/0.58  fof(f2,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.60/0.58  fof(f138,plain,(
% 1.60/0.58    ~spl3_7 | spl3_1 | ~spl3_4),
% 1.60/0.58    inference(avatar_split_clause,[],[f133,f79,f64,f135])).
% 1.60/0.58  fof(f64,plain,(
% 1.60/0.58    spl3_1 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.60/0.58  fof(f79,plain,(
% 1.60/0.58    spl3_4 <=> v1_relat_1(sK0)),
% 1.60/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.60/0.58  fof(f133,plain,(
% 1.60/0.58    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | (spl3_1 | ~spl3_4)),
% 1.60/0.58    inference(subsumption_resolution,[],[f132,f81])).
% 1.60/0.58  fof(f81,plain,(
% 1.60/0.58    v1_relat_1(sK0) | ~spl3_4),
% 1.60/0.58    inference(avatar_component_clause,[],[f79])).
% 1.60/0.58  fof(f132,plain,(
% 1.60/0.58    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | spl3_1),
% 1.60/0.58    inference(superposition,[],[f66,f46])).
% 1.60/0.58  fof(f46,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f24])).
% 1.60/0.58  fof(f24,plain,(
% 1.60/0.58    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.60/0.58    inference(ennf_transformation,[],[f16])).
% 1.60/0.58  fof(f16,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.60/0.58  fof(f66,plain,(
% 1.60/0.58    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_1),
% 1.60/0.58    inference(avatar_component_clause,[],[f64])).
% 1.60/0.58  fof(f82,plain,(
% 1.60/0.58    spl3_4),
% 1.60/0.58    inference(avatar_split_clause,[],[f39,f79])).
% 1.60/0.58  fof(f39,plain,(
% 1.60/0.58    v1_relat_1(sK0)),
% 1.60/0.58    inference(cnf_transformation,[],[f36])).
% 1.60/0.58  fof(f36,plain,(
% 1.60/0.58    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f35,f34])).
% 1.60/0.58  fof(f34,plain,(
% 1.60/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f35,plain,(
% 1.60/0.58    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f23,plain,(
% 1.60/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.60/0.58    inference(flattening,[],[f22])).
% 1.60/0.58  fof(f22,plain,(
% 1.60/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.60/0.58    inference(ennf_transformation,[],[f21])).
% 1.60/0.58  fof(f21,negated_conjecture,(
% 1.60/0.58    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.60/0.58    inference(negated_conjecture,[],[f20])).
% 1.60/0.58  fof(f20,conjecture,(
% 1.60/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.60/0.58  fof(f72,plain,(
% 1.60/0.58    spl3_2),
% 1.60/0.58    inference(avatar_split_clause,[],[f41,f69])).
% 1.60/0.58  fof(f41,plain,(
% 1.60/0.58    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.60/0.58    inference(cnf_transformation,[],[f36])).
% 1.60/0.58  fof(f67,plain,(
% 1.60/0.58    ~spl3_1),
% 1.60/0.58    inference(avatar_split_clause,[],[f42,f64])).
% 1.60/0.58  fof(f42,plain,(
% 1.60/0.58    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.60/0.58    inference(cnf_transformation,[],[f36])).
% 1.60/0.58  % SZS output end Proof for theBenchmark
% 1.60/0.58  % (31485)------------------------------
% 1.60/0.58  % (31485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (31485)Termination reason: Refutation
% 1.60/0.58  
% 1.60/0.58  % (31485)Memory used [KB]: 6524
% 1.60/0.58  % (31485)Time elapsed: 0.156 s
% 1.60/0.58  % (31485)------------------------------
% 1.60/0.58  % (31485)------------------------------
% 1.60/0.58  % (31461)Success in time 0.219 s
%------------------------------------------------------------------------------
