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
% DateTime   : Thu Dec  3 13:07:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 174 expanded)
%              Number of leaves         :   25 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  300 ( 457 expanded)
%              Number of equality atoms :   47 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f799,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f84,f130,f186,f226,f634,f706,f773,f798])).

fof(f798,plain,
    ( ~ spl3_4
    | spl3_29 ),
    inference(avatar_contradiction_clause,[],[f797])).

fof(f797,plain,
    ( $false
    | ~ spl3_4
    | spl3_29 ),
    inference(subsumption_resolution,[],[f794,f83])).

fof(f83,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f794,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_29 ),
    inference(resolution,[],[f772,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f772,plain,
    ( ~ r1_tarski(k7_relat_1(sK0,sK1),sK0)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f770])).

fof(f770,plain,
    ( spl3_29
  <=> r1_tarski(k7_relat_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f773,plain,
    ( ~ spl3_29
    | ~ spl3_4
    | spl3_27 ),
    inference(avatar_split_clause,[],[f768,f626,f81,f770])).

fof(f626,plain,
    ( spl3_27
  <=> r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f768,plain,
    ( ~ r1_tarski(k7_relat_1(sK0,sK1),sK0)
    | ~ spl3_4
    | spl3_27 ),
    inference(subsumption_resolution,[],[f767,f83])).

fof(f767,plain,
    ( ~ r1_tarski(k7_relat_1(sK0,sK1),sK0)
    | ~ v1_relat_1(sK0)
    | spl3_27 ),
    inference(duplicate_literal_removal,[],[f766])).

fof(f766,plain,
    ( ~ r1_tarski(k7_relat_1(sK0,sK1),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_27 ),
    inference(resolution,[],[f628,f153])).

fof(f153,plain,(
    ! [X6,X8,X7,X5] :
      ( r1_tarski(k3_xboole_0(X6,k10_relat_1(X5,X7)),k10_relat_1(X8,X7))
      | ~ r1_tarski(k7_relat_1(X5,X6),X8)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f144,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f144,plain,(
    ! [X6,X8,X7,X5] :
      ( r1_tarski(k3_xboole_0(X6,k10_relat_1(X5,X7)),k10_relat_1(X8,X7))
      | ~ r1_tarski(k7_relat_1(X5,X6),X8)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k7_relat_1(X5,X6))
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f53,f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).

fof(f628,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f626])).

fof(f706,plain,
    ( ~ spl3_27
    | spl3_9
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f705,f631,f127,f626])).

fof(f127,plain,
    ( spl3_9
  <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f631,plain,
    ( spl3_28
  <=> r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f705,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | spl3_9
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f704,f129])).

fof(f129,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f704,plain,
    ( k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl3_28 ),
    inference(resolution,[],[f633,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f633,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f631])).

fof(f634,plain,
    ( spl3_28
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f591,f223,f631])).

fof(f223,plain,
    ( spl3_13
  <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f591,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f225,f240])).

fof(f240,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f239,f60])).

fof(f60,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f239,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(subsumption_resolution,[],[f236,f56])).

fof(f56,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f236,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f136,f58])).

fof(f58,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f136,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f131,f56])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f54,f60])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f225,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f223])).

% (6391)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f226,plain,
    ( spl3_13
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f221,f183,f223])).

fof(f183,plain,
    ( spl3_10
  <=> r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f221,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f220,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f220,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2))
    | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f219,f60])).

fof(f219,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f218,f56])).

fof(f218,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f215,f57])).

fof(f57,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f215,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_10 ),
    inference(resolution,[],[f185,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f185,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f183])).

fof(f186,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f181,f71,f183])).

fof(f71,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f181,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f180,f57])).

fof(f180,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f172,f56])).

fof(f172,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ spl3_2 ),
    inference(superposition,[],[f115,f102])).

fof(f102,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f101,f60])).

fof(f101,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f100,f56])).

fof(f100,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f55,f61])).

fof(f61,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f115,plain,
    ( ! [X5] :
        ( r1_tarski(k9_relat_1(X5,k10_relat_1(X5,k10_relat_1(sK0,sK2))),sK1)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
    | ~ spl3_2 ),
    inference(resolution,[],[f52,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k10_relat_1(sK0,sK2))
        | r1_tarski(X0,sK1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f50,f73])).

fof(f73,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f130,plain,
    ( ~ spl3_9
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f125,f81,f66,f127])).

fof(f66,plain,
    ( spl3_1
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f125,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f121,f83])).

fof(f121,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(superposition,[],[f68,f44])).

fof(f68,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f84,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f36,f35])).

% (6396)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
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

fof(f74,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f42,f71])).

fof(f42,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43,f66])).

fof(f43,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:56:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (6381)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (6379)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (6398)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.51  % (6403)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (6389)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (6384)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (6394)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (6386)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (6380)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (6378)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (6377)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (6400)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (6382)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (6404)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (6402)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (6388)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (6393)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (6397)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (6392)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (6385)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (6395)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (6390)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (6399)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (6401)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.57  % (6398)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (6406)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f799,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f69,f74,f84,f130,f186,f226,f634,f706,f773,f798])).
% 0.22/0.57  fof(f798,plain,(
% 0.22/0.57    ~spl3_4 | spl3_29),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f797])).
% 0.22/0.57  fof(f797,plain,(
% 0.22/0.57    $false | (~spl3_4 | spl3_29)),
% 0.22/0.57    inference(subsumption_resolution,[],[f794,f83])).
% 0.22/0.57  fof(f83,plain,(
% 0.22/0.57    v1_relat_1(sK0) | ~spl3_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f81])).
% 0.22/0.57  fof(f81,plain,(
% 0.22/0.57    spl3_4 <=> v1_relat_1(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.57  fof(f794,plain,(
% 0.22/0.57    ~v1_relat_1(sK0) | spl3_29),
% 0.22/0.57    inference(resolution,[],[f772,f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.57  fof(f772,plain,(
% 0.22/0.57    ~r1_tarski(k7_relat_1(sK0,sK1),sK0) | spl3_29),
% 0.22/0.57    inference(avatar_component_clause,[],[f770])).
% 0.22/0.57  fof(f770,plain,(
% 0.22/0.57    spl3_29 <=> r1_tarski(k7_relat_1(sK0,sK1),sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.57  fof(f773,plain,(
% 0.22/0.57    ~spl3_29 | ~spl3_4 | spl3_27),
% 0.22/0.57    inference(avatar_split_clause,[],[f768,f626,f81,f770])).
% 0.22/0.57  fof(f626,plain,(
% 0.22/0.57    spl3_27 <=> r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.57  fof(f768,plain,(
% 0.22/0.57    ~r1_tarski(k7_relat_1(sK0,sK1),sK0) | (~spl3_4 | spl3_27)),
% 0.22/0.57    inference(subsumption_resolution,[],[f767,f83])).
% 0.22/0.57  fof(f767,plain,(
% 0.22/0.57    ~r1_tarski(k7_relat_1(sK0,sK1),sK0) | ~v1_relat_1(sK0) | spl3_27),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f766])).
% 0.22/0.57  fof(f766,plain,(
% 0.22/0.57    ~r1_tarski(k7_relat_1(sK0,sK1),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0) | spl3_27),
% 0.22/0.57    inference(resolution,[],[f628,f153])).
% 0.22/0.57  fof(f153,plain,(
% 0.22/0.57    ( ! [X6,X8,X7,X5] : (r1_tarski(k3_xboole_0(X6,k10_relat_1(X5,X7)),k10_relat_1(X8,X7)) | ~r1_tarski(k7_relat_1(X5,X6),X8) | ~v1_relat_1(X8) | ~v1_relat_1(X5)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f144,f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.57  fof(f144,plain,(
% 0.22/0.57    ( ! [X6,X8,X7,X5] : (r1_tarski(k3_xboole_0(X6,k10_relat_1(X5,X7)),k10_relat_1(X8,X7)) | ~r1_tarski(k7_relat_1(X5,X6),X8) | ~v1_relat_1(X8) | ~v1_relat_1(k7_relat_1(X5,X6)) | ~v1_relat_1(X5)) )),
% 0.22/0.57    inference(superposition,[],[f53,f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(flattening,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t179_relat_1)).
% 0.22/0.57  fof(f628,plain,(
% 0.22/0.57    ~r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | spl3_27),
% 0.22/0.57    inference(avatar_component_clause,[],[f626])).
% 0.22/0.57  fof(f706,plain,(
% 0.22/0.57    ~spl3_27 | spl3_9 | ~spl3_28),
% 0.22/0.57    inference(avatar_split_clause,[],[f705,f631,f127,f626])).
% 0.22/0.57  fof(f127,plain,(
% 0.22/0.57    spl3_9 <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.57  fof(f631,plain,(
% 0.22/0.57    spl3_28 <=> r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.57  fof(f705,plain,(
% 0.22/0.57    ~r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | (spl3_9 | ~spl3_28)),
% 0.22/0.57    inference(subsumption_resolution,[],[f704,f129])).
% 0.22/0.57  fof(f129,plain,(
% 0.22/0.57    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | spl3_9),
% 0.22/0.57    inference(avatar_component_clause,[],[f127])).
% 0.22/0.57  fof(f704,plain,(
% 0.22/0.57    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~r1_tarski(k3_xboole_0(sK1,k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | ~spl3_28),
% 0.22/0.57    inference(resolution,[],[f633,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(flattening,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f633,plain,(
% 0.22/0.57    r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | ~spl3_28),
% 0.22/0.57    inference(avatar_component_clause,[],[f631])).
% 0.22/0.57  fof(f634,plain,(
% 0.22/0.57    spl3_28 | ~spl3_13),
% 0.22/0.57    inference(avatar_split_clause,[],[f591,f223,f631])).
% 0.22/0.57  fof(f223,plain,(
% 0.22/0.57    spl3_13 <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.57  fof(f591,plain,(
% 0.22/0.57    r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) | ~spl3_13),
% 0.22/0.57    inference(backward_demodulation,[],[f225,f240])).
% 0.22/0.57  fof(f240,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f239,f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.57  fof(f239,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f236,f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,axiom,(
% 0.22/0.57    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.57  fof(f236,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.57    inference(superposition,[],[f136,f58])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,axiom,(
% 0.22/0.57    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.57  fof(f136,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f131,f56])).
% 0.22/0.57  fof(f131,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(superposition,[],[f54,f60])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.57  fof(f225,plain,(
% 0.22/0.57    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_13),
% 0.22/0.57    inference(avatar_component_clause,[],[f223])).
% 0.22/0.57  % (6391)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.57  fof(f226,plain,(
% 0.22/0.57    spl3_13 | ~spl3_10),
% 0.22/0.57    inference(avatar_split_clause,[],[f221,f183,f223])).
% 0.22/0.57  fof(f183,plain,(
% 0.22/0.57    spl3_10 <=> r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.57  fof(f221,plain,(
% 0.22/0.57    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_10),
% 0.22/0.57    inference(subsumption_resolution,[],[f220,f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f39])).
% 0.22/0.57  fof(f220,plain,(
% 0.22/0.57    ~r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl3_10),
% 0.22/0.57    inference(forward_demodulation,[],[f219,f60])).
% 1.54/0.57  fof(f219,plain,(
% 1.54/0.57    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~spl3_10),
% 1.54/0.57    inference(subsumption_resolution,[],[f218,f56])).
% 1.54/0.57  fof(f218,plain,(
% 1.54/0.57    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_10),
% 1.54/0.57    inference(subsumption_resolution,[],[f215,f57])).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f13])).
% 1.54/0.57  fof(f215,plain,(
% 1.54/0.57    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_10),
% 1.54/0.57    inference(resolution,[],[f185,f51])).
% 1.54/0.57  fof(f51,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f28])).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.54/0.57    inference(flattening,[],[f27])).
% 1.54/0.57  fof(f27,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.54/0.57    inference(ennf_transformation,[],[f16])).
% 1.54/0.57  fof(f16,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 1.54/0.57  fof(f185,plain,(
% 1.54/0.57    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) | ~spl3_10),
% 1.54/0.57    inference(avatar_component_clause,[],[f183])).
% 1.54/0.57  fof(f186,plain,(
% 1.54/0.57    spl3_10 | ~spl3_2),
% 1.54/0.57    inference(avatar_split_clause,[],[f181,f71,f183])).
% 1.54/0.57  fof(f71,plain,(
% 1.54/0.57    spl3_2 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.54/0.57  fof(f181,plain,(
% 1.54/0.57    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) | ~spl3_2),
% 1.54/0.57    inference(subsumption_resolution,[],[f180,f57])).
% 1.54/0.57  fof(f180,plain,(
% 1.54/0.57    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_2),
% 1.54/0.57    inference(subsumption_resolution,[],[f172,f56])).
% 1.54/0.57  fof(f172,plain,(
% 1.54/0.57    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~spl3_2),
% 1.54/0.57    inference(superposition,[],[f115,f102])).
% 1.54/0.57  fof(f102,plain,(
% 1.54/0.57    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.54/0.57    inference(forward_demodulation,[],[f101,f60])).
% 1.54/0.57  fof(f101,plain,(
% 1.54/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.54/0.57    inference(subsumption_resolution,[],[f100,f56])).
% 1.54/0.57  fof(f100,plain,(
% 1.54/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.54/0.57    inference(superposition,[],[f55,f61])).
% 1.54/0.57  fof(f61,plain,(
% 1.54/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f11])).
% 1.54/0.57  fof(f55,plain,(
% 1.54/0.57    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f34])).
% 1.54/0.57  fof(f34,plain,(
% 1.54/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.57    inference(ennf_transformation,[],[f8])).
% 1.54/0.57  fof(f8,axiom,(
% 1.54/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.54/0.57  fof(f115,plain,(
% 1.54/0.57    ( ! [X5] : (r1_tarski(k9_relat_1(X5,k10_relat_1(X5,k10_relat_1(sK0,sK2))),sK1) | ~v1_relat_1(X5) | ~v1_funct_1(X5)) ) | ~spl3_2),
% 1.54/0.57    inference(resolution,[],[f52,f97])).
% 1.54/0.57  fof(f97,plain,(
% 1.54/0.57    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK0,sK2)) | r1_tarski(X0,sK1)) ) | ~spl3_2),
% 1.54/0.57    inference(resolution,[],[f50,f73])).
% 1.54/0.57  fof(f73,plain,(
% 1.54/0.57    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_2),
% 1.54/0.57    inference(avatar_component_clause,[],[f71])).
% 1.54/0.57  fof(f50,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f26])).
% 1.54/0.57  fof(f26,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.54/0.57    inference(flattening,[],[f25])).
% 1.54/0.57  fof(f25,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.54/0.57    inference(ennf_transformation,[],[f2])).
% 1.54/0.57  fof(f2,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.54/0.57  fof(f52,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f30])).
% 1.54/0.57  fof(f30,plain,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.54/0.57    inference(flattening,[],[f29])).
% 1.54/0.57  fof(f29,plain,(
% 1.54/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.54/0.57    inference(ennf_transformation,[],[f15])).
% 1.54/0.57  fof(f15,axiom,(
% 1.54/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.54/0.57  fof(f130,plain,(
% 1.54/0.57    ~spl3_9 | spl3_1 | ~spl3_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f125,f81,f66,f127])).
% 1.54/0.57  fof(f66,plain,(
% 1.54/0.57    spl3_1 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.54/0.57  fof(f125,plain,(
% 1.54/0.57    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | (spl3_1 | ~spl3_4)),
% 1.54/0.57    inference(subsumption_resolution,[],[f121,f83])).
% 1.54/0.57  fof(f121,plain,(
% 1.54/0.57    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | spl3_1),
% 1.54/0.57    inference(superposition,[],[f68,f44])).
% 1.54/0.57  fof(f68,plain,(
% 1.54/0.57    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_1),
% 1.54/0.57    inference(avatar_component_clause,[],[f66])).
% 1.54/0.57  fof(f84,plain,(
% 1.54/0.57    spl3_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f40,f81])).
% 1.54/0.57  fof(f40,plain,(
% 1.54/0.57    v1_relat_1(sK0)),
% 1.54/0.57    inference(cnf_transformation,[],[f37])).
% 1.54/0.57  fof(f37,plain,(
% 1.54/0.57    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f36,f35])).
% 1.54/0.57  % (6396)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.54/0.57  fof(f35,plain,(
% 1.54/0.57    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f36,plain,(
% 1.54/0.57    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f21,plain,(
% 1.54/0.57    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.54/0.57    inference(flattening,[],[f20])).
% 1.54/0.57  fof(f20,plain,(
% 1.54/0.57    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f19])).
% 1.54/0.57  fof(f19,negated_conjecture,(
% 1.54/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.54/0.57    inference(negated_conjecture,[],[f18])).
% 1.54/0.57  fof(f18,conjecture,(
% 1.54/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.54/0.57  fof(f74,plain,(
% 1.54/0.57    spl3_2),
% 1.54/0.57    inference(avatar_split_clause,[],[f42,f71])).
% 1.54/0.57  fof(f42,plain,(
% 1.54/0.57    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.54/0.57    inference(cnf_transformation,[],[f37])).
% 1.54/0.57  fof(f69,plain,(
% 1.54/0.57    ~spl3_1),
% 1.54/0.57    inference(avatar_split_clause,[],[f43,f66])).
% 1.54/0.57  fof(f43,plain,(
% 1.54/0.57    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.54/0.57    inference(cnf_transformation,[],[f37])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (6398)------------------------------
% 1.54/0.57  % (6398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (6398)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (6398)Memory used [KB]: 6780
% 1.54/0.57  % (6398)Time elapsed: 0.136 s
% 1.54/0.57  % (6398)------------------------------
% 1.54/0.57  % (6398)------------------------------
% 1.54/0.58  % (6376)Success in time 0.21 s
%------------------------------------------------------------------------------
