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
% DateTime   : Thu Dec  3 12:54:06 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 253 expanded)
%              Number of leaves         :   17 (  79 expanded)
%              Depth                    :   19
%              Number of atoms          :  276 ( 663 expanded)
%              Number of equality atoms :   44 (  73 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1630,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f77,f155,f407,f537,f1624])).

fof(f1624,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f1623])).

fof(f1623,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f76,f1609])).

fof(f1609,plain,
    ( ! [X25] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X25)),X25)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(trivial_inequality_removal,[],[f1602])).

fof(f1602,plain,
    ( ! [X25] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X25)),X25) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(superposition,[],[f44,f1481])).

fof(f1481,plain,
    ( ! [X4] : k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f1480,f536])).

fof(f536,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl2_10
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f1480,plain,
    ( ! [X4] : k10_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f1479,f113])).

fof(f113,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f79,f78])).

fof(f78,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f62,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f60,f49])).

fof(f49,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f53,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f53,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f79,plain,
    ( ! [X2,X1] : r1_tarski(k4_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X2),X1)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f1479,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4))
        | k10_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f1463,f536])).

fof(f1463,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k10_relat_1(sK1,k1_xboole_0),k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4))
        | k10_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f381,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f381,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0),k10_relat_1(sK1,k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f93,f147])).

fof(f147,plain,
    ( ! [X2] : k1_xboole_0 = k9_relat_1(sK1,k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f94,f78])).

fof(f94,plain,
    ( ! [X2,X3] : k4_xboole_0(k9_relat_1(sK1,X2),k9_relat_1(sK1,X3)) = k9_relat_1(sK1,k4_xboole_0(X2,X3))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f68,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f68,plain,
    ( ! [X0,X1] : k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k4_xboole_0(X0,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f67,f39])).

fof(f67,plain,
    ( ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f66,f49])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f65,f53])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) )
    | ~ spl2_3 ),
    inference(resolution,[],[f57,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f57,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f93,plain,
    ( ! [X2,X3] : r1_tarski(k4_xboole_0(k10_relat_1(sK1,X2),X3),k10_relat_1(sK1,k9_relat_1(sK1,k4_xboole_0(k10_relat_1(sK1,X2),X3))))
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f88,f49])).

fof(f88,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK1)
        | r1_tarski(k4_xboole_0(k10_relat_1(sK1,X2),X3),k10_relat_1(sK1,k9_relat_1(sK1,k4_xboole_0(k10_relat_1(sK1,X2),X3)))) )
    | ~ spl2_1 ),
    inference(resolution,[],[f71,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f71,plain,
    ( ! [X2,X3] : r1_tarski(k4_xboole_0(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f59,f42])).

fof(f59,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f49,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl2_4
  <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f537,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f479,f405,f52,f48,f535])).

fof(f405,plain,
    ( spl2_9
  <=> k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f479,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f460,f116])).

fof(f116,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f113,f43])).

fof(f460,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f406,f85])).

fof(f85,plain,
    ( ! [X2,X3] : k4_xboole_0(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3)) = k10_relat_1(sK1,k4_xboole_0(X2,X3))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f64,f39])).

fof(f64,plain,
    ( ! [X2,X1] : k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2)) = k10_relat_1(sK1,k4_xboole_0(X1,X2))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f63,f39])).

fof(f63,plain,
    ( ! [X2,X1] : k10_relat_1(sK1,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f61,f49])).

fof(f61,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(sK1)
        | k10_relat_1(sK1,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f53,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f406,plain,
    ( k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k1_xboole_0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f405])).

fof(f407,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f278,f153,f48,f405])).

fof(f153,plain,
    ( spl2_6
  <=> k1_xboole_0 = k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f278,plain,
    ( k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(superposition,[],[f121,f154])).

fof(f154,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f121,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))
    | ~ spl2_1 ),
    inference(resolution,[],[f73,f43])).

fof(f73,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f69,f49])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) )
    | ~ spl2_1 ),
    inference(resolution,[],[f59,f38])).

fof(f155,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f146,f52,f48,f153])).

fof(f146,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f118,f62])).

fof(f118,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k1_xboole_0)
        | k1_xboole_0 = X3 )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f113,f34])).

fof(f77,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f58,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f28,f48])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:17:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (13071)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (13080)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (13079)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (13087)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (13087)Refutation not found, incomplete strategy% (13087)------------------------------
% 0.22/0.54  % (13087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13076)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (13077)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (13087)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13087)Memory used [KB]: 10618
% 0.22/0.54  % (13087)Time elapsed: 0.121 s
% 0.22/0.54  % (13087)------------------------------
% 0.22/0.54  % (13087)------------------------------
% 0.22/0.54  % (13091)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (13081)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (13095)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (13100)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (13081)Refutation not found, incomplete strategy% (13081)------------------------------
% 0.22/0.55  % (13081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13081)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13081)Memory used [KB]: 10618
% 0.22/0.55  % (13081)Time elapsed: 0.131 s
% 0.22/0.55  % (13081)------------------------------
% 0.22/0.55  % (13081)------------------------------
% 0.22/0.55  % (13100)Refutation not found, incomplete strategy% (13100)------------------------------
% 0.22/0.55  % (13100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13100)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13100)Memory used [KB]: 1663
% 0.22/0.55  % (13100)Time elapsed: 0.001 s
% 0.22/0.55  % (13100)------------------------------
% 0.22/0.55  % (13100)------------------------------
% 0.22/0.55  % (13075)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (13093)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (13078)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (13073)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (13086)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (13096)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (13090)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (13072)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.56  % (13074)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.56  % (13084)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (13085)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (13088)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (13092)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (13097)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (13094)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (13083)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (13082)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (13089)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.57  % (13083)Refutation not found, incomplete strategy% (13083)------------------------------
% 0.22/0.57  % (13083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (13083)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (13083)Memory used [KB]: 10618
% 0.22/0.57  % (13083)Time elapsed: 0.158 s
% 0.22/0.57  % (13083)------------------------------
% 0.22/0.57  % (13083)------------------------------
% 0.22/0.57  % (13098)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.57  % (13099)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.57  % (13099)Refutation not found, incomplete strategy% (13099)------------------------------
% 0.22/0.57  % (13099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (13099)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (13099)Memory used [KB]: 10618
% 0.22/0.57  % (13099)Time elapsed: 0.153 s
% 0.22/0.57  % (13099)------------------------------
% 0.22/0.57  % (13099)------------------------------
% 2.10/0.65  % (13097)Refutation found. Thanks to Tanya!
% 2.10/0.65  % SZS status Theorem for theBenchmark
% 2.10/0.65  % SZS output start Proof for theBenchmark
% 2.10/0.65  fof(f1630,plain,(
% 2.10/0.65    $false),
% 2.10/0.65    inference(avatar_sat_refutation,[],[f50,f54,f58,f77,f155,f407,f537,f1624])).
% 2.10/0.65  fof(f1624,plain,(
% 2.10/0.65    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_10),
% 2.10/0.65    inference(avatar_contradiction_clause,[],[f1623])).
% 2.10/0.65  fof(f1623,plain,(
% 2.10/0.65    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_10)),
% 2.10/0.65    inference(subsumption_resolution,[],[f76,f1609])).
% 2.10/0.65  fof(f1609,plain,(
% 2.10/0.65    ( ! [X25] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X25)),X25)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_10)),
% 2.10/0.65    inference(trivial_inequality_removal,[],[f1602])).
% 2.10/0.65  fof(f1602,plain,(
% 2.10/0.65    ( ! [X25] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X25)),X25)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_10)),
% 2.10/0.65    inference(superposition,[],[f44,f1481])).
% 2.10/0.65  fof(f1481,plain,(
% 2.10/0.65    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_10)),
% 2.10/0.65    inference(forward_demodulation,[],[f1480,f536])).
% 2.10/0.65  fof(f536,plain,(
% 2.10/0.65    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~spl2_10),
% 2.10/0.65    inference(avatar_component_clause,[],[f535])).
% 2.10/0.65  fof(f535,plain,(
% 2.10/0.65    spl2_10 <=> k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.10/0.65  fof(f1480,plain,(
% 2.10/0.65    ( ! [X4] : (k10_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_10)),
% 2.10/0.65    inference(subsumption_resolution,[],[f1479,f113])).
% 2.10/0.65  fof(f113,plain,(
% 2.10/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl2_1 | ~spl2_2)),
% 2.10/0.65    inference(superposition,[],[f79,f78])).
% 2.10/0.65  fof(f78,plain,(
% 2.10/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2)),
% 2.10/0.65    inference(resolution,[],[f62,f43])).
% 2.10/0.65  fof(f43,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.10/0.65    inference(cnf_transformation,[],[f2])).
% 2.10/0.65  fof(f2,axiom,(
% 2.10/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.10/0.65  fof(f62,plain,(
% 2.10/0.65    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2)),
% 2.10/0.65    inference(subsumption_resolution,[],[f60,f49])).
% 2.10/0.65  fof(f49,plain,(
% 2.10/0.65    v1_relat_1(sK1) | ~spl2_1),
% 2.10/0.65    inference(avatar_component_clause,[],[f48])).
% 2.10/0.65  fof(f48,plain,(
% 2.10/0.65    spl2_1 <=> v1_relat_1(sK1)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.10/0.65  fof(f60,plain,(
% 2.10/0.65    ( ! [X0] : (~v1_relat_1(sK1) | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) ) | ~spl2_2),
% 2.10/0.65    inference(resolution,[],[f53,f36])).
% 2.10/0.65  fof(f36,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f20])).
% 2.10/0.65  fof(f20,plain,(
% 2.10/0.65    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.10/0.65    inference(flattening,[],[f19])).
% 2.10/0.65  fof(f19,plain,(
% 2.10/0.65    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.10/0.65    inference(ennf_transformation,[],[f11])).
% 2.10/0.65  fof(f11,axiom,(
% 2.10/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 2.10/0.65  fof(f53,plain,(
% 2.10/0.65    v1_funct_1(sK1) | ~spl2_2),
% 2.10/0.65    inference(avatar_component_clause,[],[f52])).
% 2.10/0.65  fof(f52,plain,(
% 2.10/0.65    spl2_2 <=> v1_funct_1(sK1)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.10/0.65  fof(f79,plain,(
% 2.10/0.65    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(k9_relat_1(sK1,k10_relat_1(sK1,X1)),X2),X1)) ) | (~spl2_1 | ~spl2_2)),
% 2.10/0.65    inference(resolution,[],[f62,f42])).
% 2.10/0.65  fof(f42,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f27])).
% 2.10/0.65  fof(f27,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.10/0.65    inference(ennf_transformation,[],[f3])).
% 2.10/0.65  fof(f3,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 2.10/0.65  fof(f1479,plain,(
% 2.10/0.65    ( ! [X4] : (~r1_tarski(k1_xboole_0,k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4)) | k10_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_10)),
% 2.10/0.65    inference(forward_demodulation,[],[f1463,f536])).
% 2.10/0.65  fof(f1463,plain,(
% 2.10/0.65    ( ! [X4] : (~r1_tarski(k10_relat_1(sK1,k1_xboole_0),k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4)) | k10_relat_1(sK1,k1_xboole_0) = k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X4)),X4)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.10/0.65    inference(resolution,[],[f381,f34])).
% 2.10/0.65  fof(f34,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.10/0.65    inference(cnf_transformation,[],[f1])).
% 2.10/0.65  fof(f1,axiom,(
% 2.10/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.10/0.65  fof(f381,plain,(
% 2.10/0.65    ( ! [X0] : (r1_tarski(k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0),k10_relat_1(sK1,k1_xboole_0))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.10/0.65    inference(superposition,[],[f93,f147])).
% 2.10/0.65  fof(f147,plain,(
% 2.10/0.65    ( ! [X2] : (k1_xboole_0 = k9_relat_1(sK1,k4_xboole_0(k10_relat_1(sK1,k9_relat_1(sK1,X2)),X2))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.10/0.65    inference(superposition,[],[f94,f78])).
% 2.10/0.65  fof(f94,plain,(
% 2.10/0.65    ( ! [X2,X3] : (k4_xboole_0(k9_relat_1(sK1,X2),k9_relat_1(sK1,X3)) = k9_relat_1(sK1,k4_xboole_0(X2,X3))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.10/0.65    inference(superposition,[],[f68,f39])).
% 2.10/0.65  fof(f39,plain,(
% 2.10/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f7])).
% 2.10/0.65  fof(f7,axiom,(
% 2.10/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.10/0.65  fof(f68,plain,(
% 2.10/0.65    ( ! [X0,X1] : (k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k4_xboole_0(X0,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.10/0.65    inference(forward_demodulation,[],[f67,f39])).
% 2.10/0.65  fof(f67,plain,(
% 2.10/0.65    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 2.10/0.65    inference(subsumption_resolution,[],[f66,f49])).
% 2.10/0.65  fof(f66,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~v1_relat_1(sK1) | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | (~spl2_2 | ~spl2_3)),
% 2.10/0.65    inference(subsumption_resolution,[],[f65,f53])).
% 2.10/0.65  fof(f65,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) ) | ~spl2_3),
% 2.10/0.65    inference(resolution,[],[f57,f37])).
% 2.10/0.65  fof(f37,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f22])).
% 2.10/0.65  fof(f22,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.10/0.65    inference(flattening,[],[f21])).
% 2.10/0.65  fof(f21,plain,(
% 2.10/0.65    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.10/0.65    inference(ennf_transformation,[],[f9])).
% 2.10/0.65  fof(f9,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 2.10/0.65  fof(f57,plain,(
% 2.10/0.65    v2_funct_1(sK1) | ~spl2_3),
% 2.10/0.65    inference(avatar_component_clause,[],[f56])).
% 2.10/0.65  fof(f56,plain,(
% 2.10/0.65    spl2_3 <=> v2_funct_1(sK1)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.10/0.65  fof(f93,plain,(
% 2.10/0.65    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(k10_relat_1(sK1,X2),X3),k10_relat_1(sK1,k9_relat_1(sK1,k4_xboole_0(k10_relat_1(sK1,X2),X3))))) ) | ~spl2_1),
% 2.10/0.65    inference(subsumption_resolution,[],[f88,f49])).
% 2.10/0.65  fof(f88,plain,(
% 2.10/0.65    ( ! [X2,X3] : (~v1_relat_1(sK1) | r1_tarski(k4_xboole_0(k10_relat_1(sK1,X2),X3),k10_relat_1(sK1,k9_relat_1(sK1,k4_xboole_0(k10_relat_1(sK1,X2),X3))))) ) | ~spl2_1),
% 2.10/0.65    inference(resolution,[],[f71,f38])).
% 2.10/0.65  fof(f38,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f24])).
% 2.10/0.65  fof(f24,plain,(
% 2.10/0.65    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.10/0.65    inference(flattening,[],[f23])).
% 2.10/0.65  fof(f23,plain,(
% 2.10/0.65    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.10/0.65    inference(ennf_transformation,[],[f12])).
% 2.10/0.65  fof(f12,axiom,(
% 2.10/0.65    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.10/0.65  fof(f71,plain,(
% 2.10/0.65    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1))) ) | ~spl2_1),
% 2.10/0.65    inference(resolution,[],[f59,f42])).
% 2.10/0.65  fof(f59,plain,(
% 2.10/0.65    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) ) | ~spl2_1),
% 2.10/0.65    inference(resolution,[],[f49,f40])).
% 2.10/0.65  fof(f40,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f25])).
% 2.10/0.65  fof(f25,plain,(
% 2.10/0.65    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.10/0.65    inference(ennf_transformation,[],[f8])).
% 2.10/0.65  fof(f8,axiom,(
% 2.10/0.65    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 2.10/0.65  fof(f44,plain,(
% 2.10/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f2])).
% 2.10/0.65  fof(f76,plain,(
% 2.10/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) | spl2_4),
% 2.10/0.65    inference(avatar_component_clause,[],[f75])).
% 2.10/0.65  fof(f75,plain,(
% 2.10/0.65    spl2_4 <=> r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.10/0.65  fof(f537,plain,(
% 2.10/0.65    spl2_10 | ~spl2_1 | ~spl2_2 | ~spl2_9),
% 2.10/0.65    inference(avatar_split_clause,[],[f479,f405,f52,f48,f535])).
% 2.10/0.65  fof(f405,plain,(
% 2.10/0.65    spl2_9 <=> k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k1_xboole_0))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.10/0.65  fof(f479,plain,(
% 2.10/0.65    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | (~spl2_1 | ~spl2_2 | ~spl2_9)),
% 2.10/0.65    inference(forward_demodulation,[],[f460,f116])).
% 2.10/0.65  fof(f116,plain,(
% 2.10/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl2_1 | ~spl2_2)),
% 2.10/0.65    inference(resolution,[],[f113,f43])).
% 2.10/0.65  fof(f460,plain,(
% 2.10/0.65    k1_xboole_0 = k10_relat_1(sK1,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | (~spl2_1 | ~spl2_2 | ~spl2_9)),
% 2.10/0.65    inference(superposition,[],[f406,f85])).
% 2.10/0.65  fof(f85,plain,(
% 2.10/0.65    ( ! [X2,X3] : (k4_xboole_0(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3)) = k10_relat_1(sK1,k4_xboole_0(X2,X3))) ) | (~spl2_1 | ~spl2_2)),
% 2.10/0.65    inference(superposition,[],[f64,f39])).
% 2.10/0.65  fof(f64,plain,(
% 2.10/0.65    ( ! [X2,X1] : (k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2)) = k10_relat_1(sK1,k4_xboole_0(X1,X2))) ) | (~spl2_1 | ~spl2_2)),
% 2.10/0.65    inference(forward_demodulation,[],[f63,f39])).
% 2.10/0.65  fof(f63,plain,(
% 2.10/0.65    ( ! [X2,X1] : (k10_relat_1(sK1,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2))) ) | (~spl2_1 | ~spl2_2)),
% 2.10/0.65    inference(subsumption_resolution,[],[f61,f49])).
% 2.10/0.65  fof(f61,plain,(
% 2.10/0.65    ( ! [X2,X1] : (~v1_relat_1(sK1) | k10_relat_1(sK1,k6_subset_1(X1,X2)) = k6_subset_1(k10_relat_1(sK1,X1),k10_relat_1(sK1,X2))) ) | ~spl2_2),
% 2.10/0.65    inference(resolution,[],[f53,f35])).
% 2.10/0.65  fof(f35,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 2.10/0.65    inference(cnf_transformation,[],[f18])).
% 2.10/0.65  fof(f18,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.10/0.65    inference(flattening,[],[f17])).
% 2.10/0.65  fof(f17,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.10/0.65    inference(ennf_transformation,[],[f10])).
% 2.10/0.65  fof(f10,axiom,(
% 2.10/0.65    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 2.10/0.65  fof(f406,plain,(
% 2.10/0.65    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k1_xboole_0)) | ~spl2_9),
% 2.10/0.65    inference(avatar_component_clause,[],[f405])).
% 2.10/0.65  fof(f407,plain,(
% 2.10/0.65    spl2_9 | ~spl2_1 | ~spl2_6),
% 2.10/0.65    inference(avatar_split_clause,[],[f278,f153,f48,f405])).
% 2.10/0.65  fof(f153,plain,(
% 2.10/0.65    spl2_6 <=> k1_xboole_0 = k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.10/0.65  fof(f278,plain,(
% 2.10/0.65    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,k1_xboole_0)) | (~spl2_1 | ~spl2_6)),
% 2.10/0.65    inference(superposition,[],[f121,f154])).
% 2.10/0.65  fof(f154,plain,(
% 2.10/0.65    k1_xboole_0 = k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0)) | ~spl2_6),
% 2.10/0.65    inference(avatar_component_clause,[],[f153])).
% 2.10/0.65  fof(f121,plain,(
% 2.10/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) ) | ~spl2_1),
% 2.10/0.65    inference(resolution,[],[f73,f43])).
% 2.10/0.65  fof(f73,plain,(
% 2.10/0.65    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) ) | ~spl2_1),
% 2.10/0.65    inference(subsumption_resolution,[],[f69,f49])).
% 2.10/0.65  fof(f69,plain,(
% 2.10/0.65    ( ! [X0] : (~v1_relat_1(sK1) | r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) ) | ~spl2_1),
% 2.10/0.65    inference(resolution,[],[f59,f38])).
% 2.10/0.65  fof(f155,plain,(
% 2.10/0.65    spl2_6 | ~spl2_1 | ~spl2_2),
% 2.10/0.65    inference(avatar_split_clause,[],[f146,f52,f48,f153])).
% 2.10/0.65  fof(f146,plain,(
% 2.10/0.65    k1_xboole_0 = k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0)) | (~spl2_1 | ~spl2_2)),
% 2.10/0.65    inference(resolution,[],[f118,f62])).
% 2.10/0.65  fof(f118,plain,(
% 2.10/0.65    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) ) | (~spl2_1 | ~spl2_2)),
% 2.10/0.65    inference(resolution,[],[f113,f34])).
% 2.10/0.65  fof(f77,plain,(
% 2.10/0.65    ~spl2_4),
% 2.10/0.65    inference(avatar_split_clause,[],[f31,f75])).
% 2.10/0.65  fof(f31,plain,(
% 2.10/0.65    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 2.10/0.65    inference(cnf_transformation,[],[f16])).
% 2.10/0.65  fof(f16,plain,(
% 2.10/0.65    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.10/0.65    inference(flattening,[],[f15])).
% 2.10/0.65  fof(f15,plain,(
% 2.10/0.65    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.10/0.65    inference(ennf_transformation,[],[f14])).
% 2.10/0.65  fof(f14,negated_conjecture,(
% 2.10/0.65    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.10/0.65    inference(negated_conjecture,[],[f13])).
% 2.10/0.65  fof(f13,conjecture,(
% 2.10/0.65    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 2.10/0.65  fof(f58,plain,(
% 2.10/0.65    spl2_3),
% 2.10/0.65    inference(avatar_split_clause,[],[f30,f56])).
% 2.10/0.65  fof(f30,plain,(
% 2.10/0.65    v2_funct_1(sK1)),
% 2.10/0.65    inference(cnf_transformation,[],[f16])).
% 2.10/0.65  fof(f54,plain,(
% 2.10/0.65    spl2_2),
% 2.10/0.65    inference(avatar_split_clause,[],[f29,f52])).
% 2.10/0.65  fof(f29,plain,(
% 2.10/0.65    v1_funct_1(sK1)),
% 2.10/0.65    inference(cnf_transformation,[],[f16])).
% 2.10/0.65  fof(f50,plain,(
% 2.10/0.65    spl2_1),
% 2.10/0.65    inference(avatar_split_clause,[],[f28,f48])).
% 2.10/0.65  fof(f28,plain,(
% 2.10/0.65    v1_relat_1(sK1)),
% 2.10/0.65    inference(cnf_transformation,[],[f16])).
% 2.10/0.65  % SZS output end Proof for theBenchmark
% 2.10/0.65  % (13097)------------------------------
% 2.10/0.65  % (13097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.65  % (13097)Termination reason: Refutation
% 2.10/0.65  
% 2.10/0.65  % (13097)Memory used [KB]: 7164
% 2.10/0.65  % (13097)Time elapsed: 0.231 s
% 2.10/0.65  % (13097)------------------------------
% 2.10/0.65  % (13097)------------------------------
% 2.10/0.65  % (13070)Success in time 0.278 s
%------------------------------------------------------------------------------
