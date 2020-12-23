%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:25 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 159 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  261 ( 404 expanded)
%              Number of equality atoms :   58 (  99 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f575,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f77,f129,f316,f349,f375,f571])).

fof(f571,plain,
    ( spl3_7
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | spl3_7
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f529,f128])).

fof(f128,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_7
  <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f529,plain,
    ( k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ spl3_12 ),
    inference(superposition,[],[f374,f225])).

fof(f225,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0) ),
    inference(forward_demodulation,[],[f224,f108])).

fof(f108,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f107,f53])).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f43,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f224,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(subsumption_resolution,[],[f223,f53])).

fof(f223,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f214,f53])).

fof(f214,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f139,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f139,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f130,f53])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f45,f47])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f374,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl3_12
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f375,plain,
    ( spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f370,f346,f372])).

fof(f346,plain,
    ( spl3_9
  <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f370,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f367,f79])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f78,f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f52,f47])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f367,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f348,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f348,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f346])).

fof(f349,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f344,f313,f346])).

fof(f313,plain,
    ( spl3_8
  <=> r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f344,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f343,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f343,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2))
    | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f342,f47])).

fof(f342,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f341,f53])).

fof(f341,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f338,f54])).

fof(f54,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f338,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_8 ),
    inference(resolution,[],[f315,f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f315,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f313])).

fof(f316,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f311,f64,f313])).

fof(f64,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f311,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f310,f54])).

fof(f310,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f307,f53])).

fof(f307,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_2 ),
    inference(superposition,[],[f111,f98])).

fof(f98,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f97,f47])).

fof(f97,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f93,f53])).

fof(f93,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f46,f48])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f111,plain,
    ( ! [X5] :
        ( r1_tarski(k9_relat_1(X5,k10_relat_1(X5,k10_relat_1(sK0,sK2))),sK1)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
    | ~ spl3_2 ),
    inference(resolution,[],[f51,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k10_relat_1(sK0,sK2))
        | r1_tarski(X0,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f49,f66])).

fof(f66,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f129,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f124,f74,f59,f126])).

fof(f59,plain,
    ( spl3_1
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f74,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f124,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f123,f76])).

fof(f76,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f123,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(superposition,[],[f61,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f61,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f77,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f67,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f37,f64])).

fof(f37,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f38,f59])).

fof(f38,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.34/0.54  % (7843)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.53/0.57  % (7842)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.53/0.57  % (7841)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.53/0.58  % (7845)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.53/0.58  % (7841)Refutation not found, incomplete strategy% (7841)------------------------------
% 1.53/0.58  % (7841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (7841)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (7841)Memory used [KB]: 1663
% 1.53/0.58  % (7841)Time elapsed: 0.149 s
% 1.53/0.58  % (7841)------------------------------
% 1.53/0.58  % (7841)------------------------------
% 1.53/0.58  % (7850)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.53/0.58  % (7851)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.53/0.59  % (7857)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.53/0.59  % (7849)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.53/0.59  % (7846)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.59  % (7867)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.53/0.59  % (7863)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.53/0.59  % (7858)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.53/0.60  % (7844)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.53/0.60  % (7856)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.53/0.60  % (7869)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.53/0.60  % (7847)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.53/0.60  % (7840)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.53/0.60  % (7859)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.53/0.60  % (7852)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.53/0.60  % (7854)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.53/0.61  % (7855)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.53/0.61  % (7865)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.53/0.61  % (7868)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.53/0.61  % (7864)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.53/0.61  % (7861)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.53/0.61  % (7848)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.53/0.62  % (7866)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.53/0.62  % (7860)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.53/0.62  % (7853)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.53/0.62  % (7862)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.53/0.64  % (7861)Refutation found. Thanks to Tanya!
% 1.53/0.64  % SZS status Theorem for theBenchmark
% 1.53/0.64  % SZS output start Proof for theBenchmark
% 1.53/0.64  fof(f575,plain,(
% 1.53/0.64    $false),
% 1.53/0.64    inference(avatar_sat_refutation,[],[f62,f67,f77,f129,f316,f349,f375,f571])).
% 1.53/0.64  fof(f571,plain,(
% 1.53/0.64    spl3_7 | ~spl3_12),
% 1.53/0.64    inference(avatar_contradiction_clause,[],[f570])).
% 1.53/0.64  fof(f570,plain,(
% 1.53/0.64    $false | (spl3_7 | ~spl3_12)),
% 1.53/0.64    inference(subsumption_resolution,[],[f529,f128])).
% 1.53/0.64  fof(f128,plain,(
% 1.53/0.64    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | spl3_7),
% 1.53/0.64    inference(avatar_component_clause,[],[f126])).
% 1.53/0.64  fof(f126,plain,(
% 1.53/0.64    spl3_7 <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.53/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.53/0.64  fof(f529,plain,(
% 1.53/0.64    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~spl3_12),
% 1.53/0.64    inference(superposition,[],[f374,f225])).
% 1.53/0.64  fof(f225,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.64    inference(forward_demodulation,[],[f224,f108])).
% 1.53/0.64  fof(f108,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.53/0.64    inference(subsumption_resolution,[],[f107,f53])).
% 1.53/0.64  fof(f53,plain,(
% 1.53/0.64    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.53/0.64    inference(cnf_transformation,[],[f10])).
% 1.53/0.64  fof(f10,axiom,(
% 1.53/0.64    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.53/0.64  fof(f107,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.53/0.64    inference(superposition,[],[f43,f47])).
% 1.53/0.64  fof(f47,plain,(
% 1.53/0.64    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.53/0.64    inference(cnf_transformation,[],[f7])).
% 1.53/0.64  fof(f7,axiom,(
% 1.53/0.64    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.53/0.64  fof(f43,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.53/0.64    inference(cnf_transformation,[],[f19])).
% 1.53/0.64  fof(f19,plain,(
% 1.53/0.64    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.53/0.64    inference(ennf_transformation,[],[f8])).
% 1.53/0.64  fof(f8,axiom,(
% 1.53/0.64    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.53/0.64  fof(f224,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.53/0.64    inference(subsumption_resolution,[],[f223,f53])).
% 1.53/0.64  fof(f223,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.53/0.64    inference(subsumption_resolution,[],[f214,f53])).
% 1.53/0.64  fof(f214,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.53/0.64    inference(superposition,[],[f139,f44])).
% 1.53/0.64  fof(f44,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.53/0.64    inference(cnf_transformation,[],[f20])).
% 1.53/0.64  fof(f20,plain,(
% 1.53/0.64    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.53/0.64    inference(ennf_transformation,[],[f9])).
% 1.53/0.64  fof(f9,axiom,(
% 1.53/0.64    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.53/0.64  fof(f139,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) | ~v1_relat_1(X1)) )),
% 1.53/0.64    inference(subsumption_resolution,[],[f130,f53])).
% 1.53/0.64  fof(f130,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.53/0.64    inference(superposition,[],[f45,f47])).
% 1.53/0.64  fof(f45,plain,(
% 1.53/0.64    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.53/0.64    inference(cnf_transformation,[],[f21])).
% 1.53/0.64  fof(f21,plain,(
% 1.53/0.64    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.53/0.64    inference(ennf_transformation,[],[f6])).
% 1.53/0.64  fof(f6,axiom,(
% 1.53/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.53/0.64  fof(f374,plain,(
% 1.53/0.64    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_12),
% 1.53/0.64    inference(avatar_component_clause,[],[f372])).
% 1.53/0.64  fof(f372,plain,(
% 1.53/0.64    spl3_12 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 1.53/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.53/0.64  fof(f375,plain,(
% 1.53/0.64    spl3_12 | ~spl3_9),
% 1.53/0.64    inference(avatar_split_clause,[],[f370,f346,f372])).
% 1.53/0.64  fof(f346,plain,(
% 1.53/0.64    spl3_9 <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 1.53/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.53/0.64  fof(f370,plain,(
% 1.53/0.64    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_9),
% 1.53/0.64    inference(subsumption_resolution,[],[f367,f79])).
% 1.53/0.64  fof(f79,plain,(
% 1.53/0.64    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.53/0.64    inference(subsumption_resolution,[],[f78,f53])).
% 1.53/0.64  fof(f78,plain,(
% 1.53/0.64    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.53/0.64    inference(superposition,[],[f52,f47])).
% 1.53/0.64  fof(f52,plain,(
% 1.53/0.64    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.53/0.64    inference(cnf_transformation,[],[f29])).
% 1.53/0.64  fof(f29,plain,(
% 1.53/0.64    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.53/0.64    inference(ennf_transformation,[],[f4])).
% 1.53/0.64  fof(f4,axiom,(
% 1.53/0.64    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.53/0.64  fof(f367,plain,(
% 1.53/0.64    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) | ~spl3_9),
% 1.53/0.64    inference(resolution,[],[f348,f42])).
% 1.53/0.64  fof(f42,plain,(
% 1.53/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.53/0.64    inference(cnf_transformation,[],[f34])).
% 1.53/0.64  fof(f34,plain,(
% 1.53/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.64    inference(flattening,[],[f33])).
% 1.53/0.64  fof(f33,plain,(
% 1.53/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.64    inference(nnf_transformation,[],[f1])).
% 1.53/0.64  fof(f1,axiom,(
% 1.53/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.53/0.64  fof(f348,plain,(
% 1.53/0.64    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_9),
% 1.53/0.64    inference(avatar_component_clause,[],[f346])).
% 1.53/0.64  fof(f349,plain,(
% 1.53/0.64    spl3_9 | ~spl3_8),
% 1.53/0.64    inference(avatar_split_clause,[],[f344,f313,f346])).
% 1.53/0.64  fof(f313,plain,(
% 1.53/0.64    spl3_8 <=> r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)),
% 1.53/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.53/0.64  fof(f344,plain,(
% 1.53/0.64    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_8),
% 1.53/0.64    inference(subsumption_resolution,[],[f343,f56])).
% 1.53/0.64  fof(f56,plain,(
% 1.53/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.53/0.64    inference(equality_resolution,[],[f41])).
% 1.53/0.64  fof(f41,plain,(
% 1.53/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.53/0.64    inference(cnf_transformation,[],[f34])).
% 1.53/0.64  fof(f343,plain,(
% 1.53/0.64    ~r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_8),
% 1.53/0.64    inference(forward_demodulation,[],[f342,f47])).
% 1.53/0.64  fof(f342,plain,(
% 1.53/0.64    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~spl3_8),
% 1.53/0.64    inference(subsumption_resolution,[],[f341,f53])).
% 1.53/0.64  fof(f341,plain,(
% 1.53/0.64    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_8),
% 1.53/0.64    inference(subsumption_resolution,[],[f338,f54])).
% 1.53/0.64  fof(f54,plain,(
% 1.53/0.64    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.53/0.64    inference(cnf_transformation,[],[f10])).
% 1.53/0.64  fof(f338,plain,(
% 1.53/0.64    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_8),
% 1.53/0.64    inference(resolution,[],[f315,f50])).
% 1.53/0.64  fof(f50,plain,(
% 1.53/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.53/0.64    inference(cnf_transformation,[],[f26])).
% 1.53/0.64  fof(f26,plain,(
% 1.53/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.53/0.64    inference(flattening,[],[f25])).
% 1.53/0.64  fof(f25,plain,(
% 1.53/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.53/0.64    inference(ennf_transformation,[],[f13])).
% 1.53/0.64  fof(f13,axiom,(
% 1.53/0.64    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.53/0.64  fof(f315,plain,(
% 1.53/0.64    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) | ~spl3_8),
% 1.53/0.64    inference(avatar_component_clause,[],[f313])).
% 1.53/0.64  fof(f316,plain,(
% 1.53/0.64    spl3_8 | ~spl3_2),
% 1.53/0.64    inference(avatar_split_clause,[],[f311,f64,f313])).
% 1.53/0.64  fof(f64,plain,(
% 1.53/0.64    spl3_2 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.53/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.53/0.64  fof(f311,plain,(
% 1.53/0.64    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) | ~spl3_2),
% 1.53/0.64    inference(subsumption_resolution,[],[f310,f54])).
% 1.53/0.64  fof(f310,plain,(
% 1.53/0.64    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_2),
% 1.53/0.64    inference(subsumption_resolution,[],[f307,f53])).
% 1.53/0.64  fof(f307,plain,(
% 1.53/0.64    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_2),
% 1.53/0.64    inference(superposition,[],[f111,f98])).
% 1.53/0.64  fof(f98,plain,(
% 1.53/0.64    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.53/0.64    inference(forward_demodulation,[],[f97,f47])).
% 1.53/0.64  fof(f97,plain,(
% 1.53/0.64    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.53/0.64    inference(subsumption_resolution,[],[f93,f53])).
% 1.53/0.64  fof(f93,plain,(
% 1.53/0.64    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.53/0.64    inference(superposition,[],[f46,f48])).
% 1.53/0.64  fof(f48,plain,(
% 1.53/0.64    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.53/0.64    inference(cnf_transformation,[],[f7])).
% 1.53/0.64  fof(f46,plain,(
% 1.53/0.64    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.64    inference(cnf_transformation,[],[f22])).
% 1.53/0.64  fof(f22,plain,(
% 1.53/0.64    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.64    inference(ennf_transformation,[],[f5])).
% 1.53/0.64  fof(f5,axiom,(
% 1.53/0.64    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.53/0.64  fof(f111,plain,(
% 1.53/0.64    ( ! [X5] : (r1_tarski(k9_relat_1(X5,k10_relat_1(X5,k10_relat_1(sK0,sK2))),sK1) | ~v1_relat_1(X5) | ~v1_funct_1(X5)) ) | ~spl3_2),
% 1.53/0.64    inference(resolution,[],[f51,f101])).
% 1.53/0.64  fof(f101,plain,(
% 1.53/0.64    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK0,sK2)) | r1_tarski(X0,sK1)) ) | ~spl3_2),
% 1.53/0.64    inference(resolution,[],[f49,f66])).
% 1.53/0.64  fof(f66,plain,(
% 1.53/0.64    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_2),
% 1.53/0.64    inference(avatar_component_clause,[],[f64])).
% 1.53/0.64  fof(f49,plain,(
% 1.53/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.53/0.64    inference(cnf_transformation,[],[f24])).
% 1.53/0.64  fof(f24,plain,(
% 1.53/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.53/0.64    inference(flattening,[],[f23])).
% 1.53/0.64  fof(f23,plain,(
% 1.53/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.53/0.64    inference(ennf_transformation,[],[f2])).
% 1.53/0.64  fof(f2,axiom,(
% 1.53/0.64    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.53/0.64  fof(f51,plain,(
% 1.53/0.64    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.53/0.64    inference(cnf_transformation,[],[f28])).
% 1.53/0.64  fof(f28,plain,(
% 1.53/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.53/0.64    inference(flattening,[],[f27])).
% 1.53/0.64  fof(f27,plain,(
% 1.53/0.64    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.53/0.64    inference(ennf_transformation,[],[f12])).
% 1.53/0.64  fof(f12,axiom,(
% 1.53/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.53/0.64  fof(f129,plain,(
% 1.53/0.64    ~spl3_7 | spl3_1 | ~spl3_4),
% 1.53/0.64    inference(avatar_split_clause,[],[f124,f74,f59,f126])).
% 1.53/0.64  fof(f59,plain,(
% 1.53/0.64    spl3_1 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.53/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.53/0.64  fof(f74,plain,(
% 1.53/0.64    spl3_4 <=> v1_relat_1(sK0)),
% 1.53/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.53/0.64  fof(f124,plain,(
% 1.53/0.64    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | (spl3_1 | ~spl3_4)),
% 1.53/0.64    inference(subsumption_resolution,[],[f123,f76])).
% 1.53/0.64  fof(f76,plain,(
% 1.53/0.64    v1_relat_1(sK0) | ~spl3_4),
% 1.53/0.64    inference(avatar_component_clause,[],[f74])).
% 1.53/0.64  fof(f123,plain,(
% 1.53/0.64    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | spl3_1),
% 1.53/0.64    inference(superposition,[],[f61,f39])).
% 1.53/0.64  fof(f39,plain,(
% 1.53/0.64    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.53/0.64    inference(cnf_transformation,[],[f18])).
% 1.53/0.64  fof(f18,plain,(
% 1.53/0.64    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.53/0.64    inference(ennf_transformation,[],[f11])).
% 1.53/0.64  fof(f11,axiom,(
% 1.53/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.53/0.64  fof(f61,plain,(
% 1.53/0.64    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_1),
% 1.53/0.64    inference(avatar_component_clause,[],[f59])).
% 1.53/0.64  fof(f77,plain,(
% 1.53/0.64    spl3_4),
% 1.53/0.64    inference(avatar_split_clause,[],[f35,f74])).
% 1.53/0.64  fof(f35,plain,(
% 1.53/0.64    v1_relat_1(sK0)),
% 1.53/0.64    inference(cnf_transformation,[],[f32])).
% 1.53/0.64  fof(f32,plain,(
% 1.53/0.64    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.53/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31,f30])).
% 1.53/0.64  fof(f30,plain,(
% 1.53/0.64    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.53/0.64    introduced(choice_axiom,[])).
% 1.53/0.64  fof(f31,plain,(
% 1.53/0.64    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.53/0.64    introduced(choice_axiom,[])).
% 1.53/0.64  fof(f17,plain,(
% 1.53/0.64    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.53/0.64    inference(flattening,[],[f16])).
% 1.53/0.64  fof(f16,plain,(
% 1.53/0.64    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.53/0.64    inference(ennf_transformation,[],[f15])).
% 1.53/0.64  fof(f15,negated_conjecture,(
% 1.53/0.64    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.53/0.64    inference(negated_conjecture,[],[f14])).
% 1.53/0.64  fof(f14,conjecture,(
% 1.53/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.53/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.53/0.64  fof(f67,plain,(
% 1.53/0.64    spl3_2),
% 1.53/0.64    inference(avatar_split_clause,[],[f37,f64])).
% 1.53/0.64  fof(f37,plain,(
% 1.53/0.64    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.53/0.64    inference(cnf_transformation,[],[f32])).
% 1.53/0.64  fof(f62,plain,(
% 1.53/0.64    ~spl3_1),
% 1.53/0.64    inference(avatar_split_clause,[],[f38,f59])).
% 1.53/0.64  fof(f38,plain,(
% 1.53/0.64    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.53/0.64    inference(cnf_transformation,[],[f32])).
% 1.53/0.64  % SZS output end Proof for theBenchmark
% 1.53/0.64  % (7861)------------------------------
% 1.53/0.64  % (7861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.64  % (7861)Termination reason: Refutation
% 1.53/0.64  
% 1.53/0.64  % (7861)Memory used [KB]: 6652
% 1.53/0.64  % (7861)Time elapsed: 0.204 s
% 1.53/0.64  % (7861)------------------------------
% 1.53/0.64  % (7861)------------------------------
% 1.53/0.64  % (7839)Success in time 0.275 s
%------------------------------------------------------------------------------
