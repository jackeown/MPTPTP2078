%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:22 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 208 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  239 ( 462 expanded)
%              Number of equality atoms :   56 ( 139 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f397,f437,f997,f1245])).

fof(f1245,plain,
    ( spl5_3
    | ~ spl5_2
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f1244,f430,f77,f82])).

fof(f82,plain,
    ( spl5_3
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f77,plain,
    ( spl5_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f430,plain,
    ( spl5_47
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f1244,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_47 ),
    inference(forward_demodulation,[],[f1243,f361])).

fof(f361,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f352,f101])).

fof(f101,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f100,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f100,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f94,f41])).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f94,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f352,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0 ),
    inference(resolution,[],[f180,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1 ) ),
    inference(global_subsumption,[],[f38,f39,f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1 ) ),
    inference(superposition,[],[f53,f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f39,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1243,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl5_2
    | ~ spl5_47 ),
    inference(forward_demodulation,[],[f1229,f185])).

fof(f185,plain,
    ( ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1)))
    | ~ spl5_2 ),
    inference(resolution,[],[f65,f79])).

fof(f79,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f60,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f1229,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) = k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2)))
    | ~ spl5_47 ),
    inference(superposition,[],[f484,f432])).

fof(f432,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f430])).

fof(f484,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(forward_demodulation,[],[f267,f361])).

fof(f267,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),X1))) ),
    inference(global_subsumption,[],[f38,f266])).

fof(f266,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f261,f40])).

fof(f261,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) ) ),
    inference(resolution,[],[f64,f39])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) ) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f997,plain,(
    spl5_48 ),
    inference(avatar_contradiction_clause,[],[f981])).

fof(f981,plain,
    ( $false
    | spl5_48 ),
    inference(resolution,[],[f980,f436])).

fof(f436,plain,
    ( ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))
    | spl5_48 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl5_48
  <=> r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f980,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(duplicate_literal_removal,[],[f973])).

fof(f973,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ) ),
    inference(resolution,[],[f525,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f525,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2)
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(global_subsumption,[],[f38,f524])).

fof(f524,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2)
      | ~ v1_relat_1(k6_relat_1(X2))
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(forward_demodulation,[],[f519,f40])).

fof(f519,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4) ) ),
    inference(resolution,[],[f144,f39])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK4(k10_relat_1(X0,X1),X2),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | r1_tarski(k10_relat_1(X0,X1),X2) ) ),
    inference(resolution,[],[f68,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f437,plain,
    ( spl5_47
    | ~ spl5_48
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f413,f302,f434,f430])).

fof(f302,plain,
    ( spl5_30
  <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f413,plain,
    ( ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))
    | k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl5_30 ),
    inference(resolution,[],[f304,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f304,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f302])).

fof(f397,plain,
    ( spl5_30
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f391,f87,f302])).

fof(f87,plain,
    ( spl5_4
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f391,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f388,f89])).

fof(f89,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f388,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(global_subsumption,[],[f38,f39,f69,f387])).

fof(f387,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(forward_demodulation,[],[f386,f40])).

fof(f386,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(superposition,[],[f61,f361])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f90,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f34,f87])).

fof(f34,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f85,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f35,f82])).

fof(f35,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (5634)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (5640)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (5648)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (5632)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.57  % (5650)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.57  % (5638)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.57  % (5637)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.58  % (5636)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.58  % (5639)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.58  % (5635)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.67/0.59  % (5655)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.67/0.59  % (5647)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.67/0.60  % (5656)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.67/0.60  % (5660)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.67/0.60  % (5652)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.67/0.60  % (5643)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.67/0.60  % (5642)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.67/0.60  % (5657)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.67/0.61  % (5661)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.67/0.61  % (5654)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.67/0.61  % (5651)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.67/0.61  % (5649)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.67/0.61  % (5653)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.67/0.61  % (5633)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.67/0.61  % (5644)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.67/0.62  % (5646)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.67/0.62  % (5659)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.67/0.62  % (5658)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.67/0.62  % (5645)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.67/0.63  % (5641)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.23/0.66  % (5648)Refutation found. Thanks to Tanya!
% 2.23/0.66  % SZS status Theorem for theBenchmark
% 2.23/0.66  % SZS output start Proof for theBenchmark
% 2.23/0.66  fof(f1251,plain,(
% 2.23/0.66    $false),
% 2.23/0.66    inference(avatar_sat_refutation,[],[f80,f85,f90,f397,f437,f997,f1245])).
% 2.23/0.66  fof(f1245,plain,(
% 2.23/0.66    spl5_3 | ~spl5_2 | ~spl5_47),
% 2.23/0.66    inference(avatar_split_clause,[],[f1244,f430,f77,f82])).
% 2.23/0.66  fof(f82,plain,(
% 2.23/0.66    spl5_3 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.23/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.23/0.66  fof(f77,plain,(
% 2.23/0.66    spl5_2 <=> v1_relat_1(sK0)),
% 2.23/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.23/0.66  fof(f430,plain,(
% 2.23/0.66    spl5_47 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 2.23/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 2.23/0.66  fof(f1244,plain,(
% 2.23/0.66    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl5_2 | ~spl5_47)),
% 2.23/0.66    inference(forward_demodulation,[],[f1243,f361])).
% 2.23/0.66  fof(f361,plain,(
% 2.23/0.66    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.23/0.66    inference(forward_demodulation,[],[f352,f101])).
% 2.23/0.66  fof(f101,plain,(
% 2.23/0.66    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.23/0.66    inference(forward_demodulation,[],[f100,f40])).
% 2.23/0.66  fof(f40,plain,(
% 2.23/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.23/0.66    inference(cnf_transformation,[],[f7])).
% 2.23/0.66  fof(f7,axiom,(
% 2.23/0.66    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.23/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.23/0.66  fof(f100,plain,(
% 2.23/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 2.23/0.66    inference(forward_demodulation,[],[f94,f41])).
% 2.23/0.67  fof(f41,plain,(
% 2.23/0.67    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.23/0.67    inference(cnf_transformation,[],[f7])).
% 2.23/0.67  fof(f94,plain,(
% 2.23/0.67    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 2.23/0.67    inference(resolution,[],[f42,f38])).
% 2.23/0.67  fof(f38,plain,(
% 2.23/0.67    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f9])).
% 2.23/0.67  fof(f9,axiom,(
% 2.23/0.67    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.23/0.67  fof(f42,plain,(
% 2.23/0.67    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f19])).
% 2.23/0.67  fof(f19,plain,(
% 2.23/0.67    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.23/0.67    inference(ennf_transformation,[],[f6])).
% 2.23/0.67  fof(f6,axiom,(
% 2.23/0.67    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.23/0.67  fof(f352,plain,(
% 2.23/0.67    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X0)) = X0) )),
% 2.23/0.67    inference(resolution,[],[f180,f69])).
% 2.23/0.67  fof(f69,plain,(
% 2.23/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.23/0.67    inference(equality_resolution,[],[f55])).
% 2.23/0.67  fof(f55,plain,(
% 2.23/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.23/0.67    inference(cnf_transformation,[],[f2])).
% 2.23/0.67  fof(f2,axiom,(
% 2.23/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.23/0.67  fof(f180,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1) )),
% 2.23/0.67    inference(global_subsumption,[],[f38,f39,f174])).
% 2.23/0.67  fof(f174,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = X1) )),
% 2.23/0.67    inference(superposition,[],[f53,f41])).
% 2.23/0.67  fof(f53,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 2.23/0.67    inference(cnf_transformation,[],[f27])).
% 2.23/0.67  fof(f27,plain,(
% 2.23/0.67    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.23/0.67    inference(flattening,[],[f26])).
% 2.23/0.67  fof(f26,plain,(
% 2.23/0.67    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.23/0.67    inference(ennf_transformation,[],[f12])).
% 2.23/0.67  fof(f12,axiom,(
% 2.23/0.67    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 2.23/0.67  fof(f39,plain,(
% 2.23/0.67    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f9])).
% 2.23/0.67  fof(f1243,plain,(
% 2.23/0.67    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | (~spl5_2 | ~spl5_47)),
% 2.23/0.67    inference(forward_demodulation,[],[f1229,f185])).
% 2.23/0.67  fof(f185,plain,(
% 2.23/0.67    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1)))) ) | ~spl5_2),
% 2.23/0.67    inference(resolution,[],[f65,f79])).
% 2.23/0.67  fof(f79,plain,(
% 2.23/0.67    v1_relat_1(sK0) | ~spl5_2),
% 2.23/0.67    inference(avatar_component_clause,[],[f77])).
% 2.23/0.67  fof(f65,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 2.23/0.67    inference(definition_unfolding,[],[f60,f63])).
% 2.23/0.67  fof(f63,plain,(
% 2.23/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.23/0.67    inference(definition_unfolding,[],[f49,f50])).
% 2.23/0.67  fof(f50,plain,(
% 2.23/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f4])).
% 2.23/0.67  fof(f4,axiom,(
% 2.23/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.23/0.67  fof(f49,plain,(
% 2.23/0.67    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f5])).
% 2.23/0.67  fof(f5,axiom,(
% 2.23/0.67    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.23/0.67  fof(f60,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f29])).
% 2.23/0.67  fof(f29,plain,(
% 2.23/0.67    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.23/0.67    inference(ennf_transformation,[],[f10])).
% 2.23/0.67  fof(f10,axiom,(
% 2.23/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 2.23/0.67  fof(f1229,plain,(
% 2.23/0.67    k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) = k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2))) | ~spl5_47),
% 2.23/0.67    inference(superposition,[],[f484,f432])).
% 2.23/0.67  fof(f432,plain,(
% 2.23/0.67    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl5_47),
% 2.23/0.67    inference(avatar_component_clause,[],[f430])).
% 2.23/0.67  fof(f484,plain,(
% 2.23/0.67    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1))) )),
% 2.23/0.67    inference(forward_demodulation,[],[f267,f361])).
% 2.23/0.67  fof(f267,plain,(
% 2.23/0.67    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),X1)))) )),
% 2.23/0.67    inference(global_subsumption,[],[f38,f266])).
% 2.23/0.67  fof(f266,plain,(
% 2.23/0.67    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.23/0.67    inference(forward_demodulation,[],[f261,f40])).
% 2.23/0.67  fof(f261,plain,(
% 2.23/0.67    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))))) )),
% 2.23/0.67    inference(resolution,[],[f64,f39])).
% 2.23/0.67  fof(f64,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1))))) )),
% 2.23/0.67    inference(definition_unfolding,[],[f52,f63])).
% 2.23/0.67  fof(f52,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f25])).
% 2.23/0.67  fof(f25,plain,(
% 2.23/0.67    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.23/0.67    inference(flattening,[],[f24])).
% 2.23/0.67  fof(f24,plain,(
% 2.23/0.67    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.23/0.67    inference(ennf_transformation,[],[f13])).
% 2.23/0.67  fof(f13,axiom,(
% 2.23/0.67    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 2.23/0.67  fof(f997,plain,(
% 2.23/0.67    spl5_48),
% 2.23/0.67    inference(avatar_contradiction_clause,[],[f981])).
% 2.23/0.67  fof(f981,plain,(
% 2.23/0.67    $false | spl5_48),
% 2.23/0.67    inference(resolution,[],[f980,f436])).
% 2.23/0.67  fof(f436,plain,(
% 2.23/0.67    ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) | spl5_48),
% 2.23/0.67    inference(avatar_component_clause,[],[f434])).
% 2.23/0.67  fof(f434,plain,(
% 2.23/0.67    spl5_48 <=> r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))),
% 2.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 2.23/0.67  fof(f980,plain,(
% 2.23/0.67    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.23/0.67    inference(duplicate_literal_removal,[],[f973])).
% 2.23/0.67  fof(f973,plain,(
% 2.23/0.67    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.23/0.67    inference(resolution,[],[f525,f59])).
% 2.23/0.67  fof(f59,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f28])).
% 2.23/0.67  fof(f28,plain,(
% 2.23/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f1])).
% 2.23/0.67  fof(f1,axiom,(
% 2.23/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.23/0.67  fof(f525,plain,(
% 2.23/0.67    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.23/0.67    inference(global_subsumption,[],[f38,f524])).
% 2.23/0.67  fof(f524,plain,(
% 2.23/0.67    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),X2) | ~v1_relat_1(k6_relat_1(X2)) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.23/0.67    inference(forward_demodulation,[],[f519,f40])).
% 2.23/0.67  fof(f519,plain,(
% 2.23/0.67    ( ! [X4,X2,X3] : (r2_hidden(sK4(k10_relat_1(k6_relat_1(X2),X3),X4),k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | r1_tarski(k10_relat_1(k6_relat_1(X2),X3),X4)) )),
% 2.23/0.67    inference(resolution,[],[f144,f39])).
% 2.23/0.67  fof(f144,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK4(k10_relat_1(X0,X1),X2),k1_relat_1(X0)) | ~v1_relat_1(X0) | r1_tarski(k10_relat_1(X0,X1),X2)) )),
% 2.23/0.67    inference(resolution,[],[f68,f58])).
% 2.23/0.67  fof(f58,plain,(
% 2.23/0.67    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.23/0.67    inference(cnf_transformation,[],[f28])).
% 2.23/0.67  fof(f68,plain,(
% 2.23/0.67    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.23/0.67    inference(equality_resolution,[],[f46])).
% 2.23/0.67  fof(f46,plain,(
% 2.23/0.67    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 2.23/0.67    inference(cnf_transformation,[],[f21])).
% 2.23/0.67  fof(f21,plain,(
% 2.23/0.67    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.23/0.67    inference(flattening,[],[f20])).
% 2.23/0.67  fof(f20,plain,(
% 2.23/0.67    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f8])).
% 2.23/0.67  fof(f8,axiom,(
% 2.23/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).
% 2.23/0.67  fof(f437,plain,(
% 2.23/0.67    spl5_47 | ~spl5_48 | ~spl5_30),
% 2.23/0.67    inference(avatar_split_clause,[],[f413,f302,f434,f430])).
% 2.23/0.67  fof(f302,plain,(
% 2.23/0.67    spl5_30 <=> r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 2.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.23/0.67  fof(f413,plain,(
% 2.23/0.67    ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) | k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl5_30),
% 2.23/0.67    inference(resolution,[],[f304,f56])).
% 2.23/0.67  fof(f56,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.23/0.67    inference(cnf_transformation,[],[f2])).
% 2.23/0.67  fof(f304,plain,(
% 2.23/0.67    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl5_30),
% 2.23/0.67    inference(avatar_component_clause,[],[f302])).
% 2.23/0.67  fof(f397,plain,(
% 2.23/0.67    spl5_30 | ~spl5_4),
% 2.23/0.67    inference(avatar_split_clause,[],[f391,f87,f302])).
% 2.23/0.67  fof(f87,plain,(
% 2.23/0.67    spl5_4 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.23/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.23/0.67  fof(f391,plain,(
% 2.23/0.67    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~spl5_4),
% 2.23/0.67    inference(resolution,[],[f388,f89])).
% 2.23/0.67  fof(f89,plain,(
% 2.23/0.67    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl5_4),
% 2.23/0.67    inference(avatar_component_clause,[],[f87])).
% 2.23/0.67  fof(f388,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.23/0.67    inference(global_subsumption,[],[f38,f39,f69,f387])).
% 2.23/0.67  fof(f387,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X0) | ~r1_tarski(X0,X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.23/0.67    inference(forward_demodulation,[],[f386,f40])).
% 2.23/0.67  fof(f386,plain,(
% 2.23/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_funct_1(k6_relat_1(X0)) | ~r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 2.23/0.67    inference(superposition,[],[f61,f361])).
% 2.23/0.67  fof(f61,plain,(
% 2.23/0.67    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_relat_1(X2) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 2.23/0.67    inference(cnf_transformation,[],[f31])).
% 2.23/0.67  fof(f31,plain,(
% 2.23/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.23/0.67    inference(flattening,[],[f30])).
% 2.23/0.67  fof(f30,plain,(
% 2.23/0.67    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.23/0.67    inference(ennf_transformation,[],[f14])).
% 2.23/0.67  fof(f14,axiom,(
% 2.23/0.67    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 2.23/0.67  fof(f90,plain,(
% 2.23/0.67    spl5_4),
% 2.23/0.67    inference(avatar_split_clause,[],[f34,f87])).
% 2.23/0.67  fof(f34,plain,(
% 2.23/0.67    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.23/0.67    inference(cnf_transformation,[],[f18])).
% 2.23/0.67  fof(f18,plain,(
% 2.23/0.67    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.23/0.67    inference(flattening,[],[f17])).
% 2.23/0.67  fof(f17,plain,(
% 2.23/0.67    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.23/0.67    inference(ennf_transformation,[],[f16])).
% 2.23/0.67  fof(f16,negated_conjecture,(
% 2.23/0.67    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.23/0.67    inference(negated_conjecture,[],[f15])).
% 2.23/0.67  fof(f15,conjecture,(
% 2.23/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.23/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 2.23/0.67  fof(f85,plain,(
% 2.23/0.67    ~spl5_3),
% 2.23/0.67    inference(avatar_split_clause,[],[f35,f82])).
% 2.23/0.67  fof(f35,plain,(
% 2.23/0.67    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.23/0.67    inference(cnf_transformation,[],[f18])).
% 2.23/0.67  fof(f80,plain,(
% 2.23/0.67    spl5_2),
% 2.23/0.67    inference(avatar_split_clause,[],[f36,f77])).
% 2.23/0.67  fof(f36,plain,(
% 2.23/0.67    v1_relat_1(sK0)),
% 2.23/0.67    inference(cnf_transformation,[],[f18])).
% 2.23/0.67  % SZS output end Proof for theBenchmark
% 2.23/0.67  % (5648)------------------------------
% 2.23/0.67  % (5648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.23/0.67  % (5648)Termination reason: Refutation
% 2.23/0.67  
% 2.23/0.67  % (5648)Memory used [KB]: 11641
% 2.23/0.67  % (5648)Time elapsed: 0.225 s
% 2.23/0.67  % (5648)------------------------------
% 2.23/0.67  % (5648)------------------------------
% 2.35/0.68  % (5631)Success in time 0.308 s
%------------------------------------------------------------------------------
