%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:26 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 197 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  260 ( 501 expanded)
%              Number of equality atoms :   59 ( 143 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f743,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f85,f138,f553,f566,f716])).

fof(f716,plain,
    ( spl3_7
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f715])).

fof(f715,plain,
    ( $false
    | spl3_7
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f714,f137])).

fof(f137,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_7
  <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f714,plain,
    ( k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f703,f153])).

fof(f153,plain,(
    ! [X1] : k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(subsumption_resolution,[],[f152,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f152,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,X1)
      | k9_relat_1(k6_relat_1(X1),X1) = X1 ) ),
    inference(forward_demodulation,[],[f151,f53])).

fof(f53,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f151,plain,(
    ! [X1] :
      ( k9_relat_1(k6_relat_1(X1),X1) = X1
      | ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X1))) ) ),
    inference(subsumption_resolution,[],[f150,f59])).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f150,plain,(
    ! [X1] :
      ( k9_relat_1(k6_relat_1(X1),X1) = X1
      | ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f146,f60])).

fof(f60,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f146,plain,(
    ! [X1] :
      ( k9_relat_1(k6_relat_1(X1),X1) = X1
      | ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X1)))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f48,f107])).

fof(f107,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f106,f52])).

fof(f52,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f106,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f102,f59])).

fof(f102,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f51,f53])).

fof(f51,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f703,plain,
    ( k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl3_12 ),
    inference(superposition,[],[f468,f565])).

fof(f565,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f563])).

fof(f563,plain,
    ( spl3_12
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f468,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(backward_demodulation,[],[f158,f153])).

fof(f158,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) ),
    inference(subsumption_resolution,[],[f157,f59])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f154,f60])).

fof(f154,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f49,f52])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f566,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f561,f550,f563])).

fof(f550,plain,
    ( spl3_11
  <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f561,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f558,f87])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f86,f59])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f57,f52])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f558,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_11 ),
    inference(resolution,[],[f552,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f552,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f550])).

fof(f553,plain,
    ( spl3_11
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f548,f72,f550])).

fof(f72,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f548,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f547,f59])).

fof(f547,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f542,f60])).

fof(f542,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_2 ),
    inference(superposition,[],[f460,f107])).

fof(f460,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f459,f57])).

fof(f459,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1))
        | ~ r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0)) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f451])).

fof(f451,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1))
        | ~ r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f223,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f223,plain,
    ( ! [X7] :
        ( r1_tarski(k9_relat_1(X7,k10_relat_1(X7,k10_relat_1(sK0,sK2))),sK1)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
    | ~ spl3_2 ),
    inference(resolution,[],[f155,f114])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k10_relat_1(sK0,sK2))
        | r1_tarski(X0,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f74])).

fof(f74,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f155,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f58,f49])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f138,plain,
    ( ~ spl3_7
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f133,f82,f67,f135])).

fof(f67,plain,
    ( spl3_1
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f82,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f133,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f132,f84])).

fof(f84,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f132,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(superposition,[],[f69,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f69,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f85,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f75,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f42,f72])).

fof(f42,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43,f67])).

fof(f43,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:38:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (2399)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.49  % (2408)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (2389)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (2393)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (2394)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (2416)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (2407)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (2396)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (2404)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (2391)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (2412)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (2418)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (2419)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (2398)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (2410)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (2417)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (2395)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (2392)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.55  % (2411)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (2415)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (2409)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (2401)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (2390)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.55  % (2403)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (2397)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (2400)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (2414)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.56  % (2406)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.57  % (2413)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.57  % (2405)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.84/0.60  % (2411)Refutation found. Thanks to Tanya!
% 1.84/0.60  % SZS status Theorem for theBenchmark
% 1.84/0.60  % SZS output start Proof for theBenchmark
% 1.84/0.60  fof(f743,plain,(
% 1.84/0.60    $false),
% 1.84/0.60    inference(avatar_sat_refutation,[],[f70,f75,f85,f138,f553,f566,f716])).
% 1.84/0.60  fof(f716,plain,(
% 1.84/0.60    spl3_7 | ~spl3_12),
% 1.84/0.60    inference(avatar_contradiction_clause,[],[f715])).
% 1.84/0.60  fof(f715,plain,(
% 1.84/0.60    $false | (spl3_7 | ~spl3_12)),
% 1.84/0.60    inference(subsumption_resolution,[],[f714,f137])).
% 1.84/0.60  fof(f137,plain,(
% 1.84/0.60    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | spl3_7),
% 1.84/0.60    inference(avatar_component_clause,[],[f135])).
% 1.84/0.60  fof(f135,plain,(
% 1.84/0.60    spl3_7 <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.84/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.84/0.60  fof(f714,plain,(
% 1.84/0.60    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~spl3_12),
% 1.84/0.60    inference(forward_demodulation,[],[f703,f153])).
% 1.84/0.60  fof(f153,plain,(
% 1.84/0.60    ( ! [X1] : (k9_relat_1(k6_relat_1(X1),X1) = X1) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f152,f64])).
% 1.84/0.60  fof(f64,plain,(
% 1.84/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.84/0.60    inference(equality_resolution,[],[f46])).
% 1.84/0.60  fof(f46,plain,(
% 1.84/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f39,plain,(
% 1.84/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.60    inference(flattening,[],[f38])).
% 1.84/0.60  fof(f38,plain,(
% 1.84/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.60    inference(nnf_transformation,[],[f1])).
% 1.84/0.60  fof(f1,axiom,(
% 1.84/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.84/0.60  fof(f152,plain,(
% 1.84/0.60    ( ! [X1] : (~r1_tarski(X1,X1) | k9_relat_1(k6_relat_1(X1),X1) = X1) )),
% 1.84/0.60    inference(forward_demodulation,[],[f151,f53])).
% 1.84/0.60  fof(f53,plain,(
% 1.84/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.84/0.60    inference(cnf_transformation,[],[f10])).
% 1.84/0.60  fof(f10,axiom,(
% 1.84/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.84/0.60  fof(f151,plain,(
% 1.84/0.60    ( ! [X1] : (k9_relat_1(k6_relat_1(X1),X1) = X1 | ~r1_tarski(X1,k2_relat_1(k6_relat_1(X1)))) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f150,f59])).
% 1.84/0.60  fof(f59,plain,(
% 1.84/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.84/0.60    inference(cnf_transformation,[],[f12])).
% 1.84/0.60  fof(f12,axiom,(
% 1.84/0.60    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.84/0.60  fof(f150,plain,(
% 1.84/0.60    ( ! [X1] : (k9_relat_1(k6_relat_1(X1),X1) = X1 | ~r1_tarski(X1,k2_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f146,f60])).
% 1.84/0.60  fof(f60,plain,(
% 1.84/0.60    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.84/0.60    inference(cnf_transformation,[],[f12])).
% 1.84/0.60  fof(f146,plain,(
% 1.84/0.60    ( ! [X1] : (k9_relat_1(k6_relat_1(X1),X1) = X1 | ~r1_tarski(X1,k2_relat_1(k6_relat_1(X1))) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.84/0.60    inference(superposition,[],[f48,f107])).
% 1.84/0.60  fof(f107,plain,(
% 1.84/0.60    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.84/0.60    inference(forward_demodulation,[],[f106,f52])).
% 1.84/0.60  fof(f52,plain,(
% 1.84/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.84/0.60    inference(cnf_transformation,[],[f10])).
% 1.84/0.60  fof(f106,plain,(
% 1.84/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f102,f59])).
% 1.84/0.60  fof(f102,plain,(
% 1.84/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.84/0.60    inference(superposition,[],[f51,f53])).
% 1.84/0.60  fof(f51,plain,(
% 1.84/0.60    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f28])).
% 1.84/0.60  fof(f28,plain,(
% 1.84/0.60    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.84/0.60    inference(ennf_transformation,[],[f9])).
% 1.84/0.60  fof(f9,axiom,(
% 1.84/0.60    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.84/0.60  fof(f48,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f24])).
% 1.84/0.60  fof(f24,plain,(
% 1.84/0.60    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.84/0.60    inference(flattening,[],[f23])).
% 1.84/0.60  fof(f23,plain,(
% 1.84/0.60    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.84/0.60    inference(ennf_transformation,[],[f14])).
% 1.84/0.60  fof(f14,axiom,(
% 1.84/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 1.84/0.60  fof(f703,plain,(
% 1.84/0.60    k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | ~spl3_12),
% 1.84/0.60    inference(superposition,[],[f468,f565])).
% 1.84/0.60  fof(f565,plain,(
% 1.84/0.60    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_12),
% 1.84/0.60    inference(avatar_component_clause,[],[f563])).
% 1.84/0.60  fof(f563,plain,(
% 1.84/0.60    spl3_12 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 1.84/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.84/0.60  fof(f468,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1))) )),
% 1.84/0.60    inference(backward_demodulation,[],[f158,f153])).
% 1.84/0.60  fof(f158,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f157,f59])).
% 1.84/0.60  fof(f157,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f154,f60])).
% 1.84/0.60  fof(f154,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.84/0.60    inference(superposition,[],[f49,f52])).
% 1.84/0.60  fof(f49,plain,(
% 1.84/0.60    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f26])).
% 1.84/0.60  fof(f26,plain,(
% 1.84/0.60    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.84/0.60    inference(flattening,[],[f25])).
% 1.84/0.60  fof(f25,plain,(
% 1.84/0.60    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.84/0.60    inference(ennf_transformation,[],[f15])).
% 1.84/0.60  fof(f15,axiom,(
% 1.84/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 1.84/0.60  fof(f566,plain,(
% 1.84/0.60    spl3_12 | ~spl3_11),
% 1.84/0.60    inference(avatar_split_clause,[],[f561,f550,f563])).
% 1.84/0.60  fof(f550,plain,(
% 1.84/0.60    spl3_11 <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 1.84/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.84/0.60  fof(f561,plain,(
% 1.84/0.60    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_11),
% 1.84/0.60    inference(subsumption_resolution,[],[f558,f87])).
% 1.84/0.60  fof(f87,plain,(
% 1.84/0.60    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.84/0.60    inference(subsumption_resolution,[],[f86,f59])).
% 1.84/0.60  fof(f86,plain,(
% 1.84/0.60    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.84/0.60    inference(superposition,[],[f57,f52])).
% 1.84/0.60  fof(f57,plain,(
% 1.84/0.60    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f34])).
% 1.84/0.60  fof(f34,plain,(
% 1.84/0.60    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.84/0.60    inference(ennf_transformation,[],[f8])).
% 1.84/0.60  fof(f8,axiom,(
% 1.84/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.84/0.60  fof(f558,plain,(
% 1.84/0.60    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) | ~spl3_11),
% 1.84/0.60    inference(resolution,[],[f552,f47])).
% 1.84/0.60  fof(f47,plain,(
% 1.84/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f552,plain,(
% 1.84/0.60    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_11),
% 1.84/0.60    inference(avatar_component_clause,[],[f550])).
% 1.84/0.60  fof(f553,plain,(
% 1.84/0.60    spl3_11 | ~spl3_2),
% 1.84/0.60    inference(avatar_split_clause,[],[f548,f72,f550])).
% 1.84/0.60  fof(f72,plain,(
% 1.84/0.60    spl3_2 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.84/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.84/0.60  fof(f548,plain,(
% 1.84/0.60    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_2),
% 1.84/0.60    inference(subsumption_resolution,[],[f547,f59])).
% 1.84/0.60  fof(f547,plain,(
% 1.84/0.60    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_2),
% 1.84/0.60    inference(subsumption_resolution,[],[f542,f60])).
% 1.84/0.60  fof(f542,plain,(
% 1.84/0.60    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_2),
% 1.84/0.60    inference(superposition,[],[f460,f107])).
% 1.84/0.60  fof(f460,plain,(
% 1.84/0.60    ( ! [X0] : (r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_2),
% 1.84/0.60    inference(subsumption_resolution,[],[f459,f57])).
% 1.84/0.60  fof(f459,plain,(
% 1.84/0.60    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1)) | ~r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0))) ) | ~spl3_2),
% 1.84/0.60    inference(duplicate_literal_removal,[],[f451])).
% 1.84/0.60  fof(f451,plain,(
% 1.84/0.60    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k10_relat_1(X0,sK1)) | ~r1_tarski(k10_relat_1(X0,k10_relat_1(sK0,sK2)),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_2),
% 1.84/0.60    inference(resolution,[],[f223,f56])).
% 1.84/0.60  fof(f56,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f33])).
% 1.84/0.60  fof(f33,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.84/0.60    inference(flattening,[],[f32])).
% 1.84/0.60  fof(f32,plain,(
% 1.84/0.60    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.84/0.60    inference(ennf_transformation,[],[f16])).
% 1.84/0.60  fof(f16,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 1.84/0.60  fof(f223,plain,(
% 1.84/0.60    ( ! [X7] : (r1_tarski(k9_relat_1(X7,k10_relat_1(X7,k10_relat_1(sK0,sK2))),sK1) | ~v1_relat_1(X7) | ~v1_funct_1(X7)) ) | ~spl3_2),
% 1.84/0.60    inference(resolution,[],[f155,f114])).
% 1.84/0.60  fof(f114,plain,(
% 1.84/0.60    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK0,sK2)) | r1_tarski(X0,sK1)) ) | ~spl3_2),
% 1.84/0.60    inference(resolution,[],[f55,f74])).
% 1.84/0.60  fof(f74,plain,(
% 1.84/0.60    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_2),
% 1.84/0.60    inference(avatar_component_clause,[],[f72])).
% 1.84/0.60  fof(f55,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f31])).
% 1.84/0.60  fof(f31,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.84/0.60    inference(flattening,[],[f30])).
% 1.84/0.60  fof(f30,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.84/0.60    inference(ennf_transformation,[],[f3])).
% 1.84/0.60  fof(f3,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.84/0.60  fof(f155,plain,(
% 1.84/0.60    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.84/0.60    inference(superposition,[],[f58,f49])).
% 1.84/0.60  fof(f58,plain,(
% 1.84/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f2])).
% 1.84/0.60  fof(f2,axiom,(
% 1.84/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.84/0.60  fof(f138,plain,(
% 1.84/0.60    ~spl3_7 | spl3_1 | ~spl3_4),
% 1.84/0.60    inference(avatar_split_clause,[],[f133,f82,f67,f135])).
% 1.84/0.60  fof(f67,plain,(
% 1.84/0.60    spl3_1 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.84/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.84/0.60  fof(f82,plain,(
% 1.84/0.60    spl3_4 <=> v1_relat_1(sK0)),
% 1.84/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.84/0.60  fof(f133,plain,(
% 1.84/0.60    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | (spl3_1 | ~spl3_4)),
% 1.84/0.60    inference(subsumption_resolution,[],[f132,f84])).
% 1.84/0.60  fof(f84,plain,(
% 1.84/0.60    v1_relat_1(sK0) | ~spl3_4),
% 1.84/0.60    inference(avatar_component_clause,[],[f82])).
% 1.84/0.60  fof(f132,plain,(
% 1.84/0.60    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | spl3_1),
% 1.84/0.60    inference(superposition,[],[f69,f44])).
% 1.84/0.60  fof(f44,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f22])).
% 1.84/0.60  fof(f22,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.84/0.60    inference(ennf_transformation,[],[f13])).
% 1.84/0.60  fof(f13,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.84/0.60  fof(f69,plain,(
% 1.84/0.60    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_1),
% 1.84/0.60    inference(avatar_component_clause,[],[f67])).
% 1.84/0.60  fof(f85,plain,(
% 1.84/0.60    spl3_4),
% 1.84/0.60    inference(avatar_split_clause,[],[f40,f82])).
% 1.84/0.60  fof(f40,plain,(
% 1.84/0.60    v1_relat_1(sK0)),
% 1.84/0.60    inference(cnf_transformation,[],[f37])).
% 1.84/0.60  fof(f37,plain,(
% 1.84/0.60    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.84/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f36,f35])).
% 1.84/0.60  fof(f35,plain,(
% 1.84/0.60    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.84/0.60    introduced(choice_axiom,[])).
% 1.84/0.60  fof(f36,plain,(
% 1.84/0.60    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.84/0.60    introduced(choice_axiom,[])).
% 1.84/0.60  fof(f21,plain,(
% 1.84/0.60    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.84/0.60    inference(flattening,[],[f20])).
% 1.84/0.60  fof(f20,plain,(
% 1.84/0.60    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.84/0.60    inference(ennf_transformation,[],[f19])).
% 1.84/0.60  fof(f19,negated_conjecture,(
% 1.84/0.60    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.84/0.60    inference(negated_conjecture,[],[f18])).
% 1.84/0.60  fof(f18,conjecture,(
% 1.84/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.84/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.84/0.60  fof(f75,plain,(
% 1.84/0.60    spl3_2),
% 1.84/0.60    inference(avatar_split_clause,[],[f42,f72])).
% 1.84/0.60  fof(f42,plain,(
% 1.84/0.60    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.84/0.60    inference(cnf_transformation,[],[f37])).
% 1.84/0.60  fof(f70,plain,(
% 1.84/0.60    ~spl3_1),
% 1.84/0.60    inference(avatar_split_clause,[],[f43,f67])).
% 1.84/0.60  fof(f43,plain,(
% 1.84/0.60    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.84/0.60    inference(cnf_transformation,[],[f37])).
% 1.84/0.60  % SZS output end Proof for theBenchmark
% 1.84/0.60  % (2411)------------------------------
% 1.84/0.60  % (2411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (2411)Termination reason: Refutation
% 1.84/0.60  
% 1.84/0.60  % (2411)Memory used [KB]: 6652
% 1.84/0.60  % (2411)Time elapsed: 0.184 s
% 1.84/0.60  % (2411)------------------------------
% 1.84/0.60  % (2411)------------------------------
% 1.84/0.60  % (2388)Success in time 0.249 s
%------------------------------------------------------------------------------
