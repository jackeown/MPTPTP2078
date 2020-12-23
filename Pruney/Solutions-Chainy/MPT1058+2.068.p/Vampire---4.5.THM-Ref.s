%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:26 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 192 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  187 ( 476 expanded)
%              Number of equality atoms :   56 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f60,f65,f323,f1166])).

fof(f1166,plain,
    ( ~ spl3_1
    | spl3_4
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f1165])).

fof(f1165,plain,
    ( $false
    | ~ spl3_1
    | spl3_4
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f1164,f64])).

fof(f64,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_4
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1164,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f1163,f158])).

fof(f158,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f69,f108,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f108,plain,(
    ! [X0] : r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X0)) ),
    inference(forward_demodulation,[],[f107,f75])).

fof(f75,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f74,f34])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f74,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f71,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f31,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f107,plain,(
    ! [X0] : r1_tarski(X0,k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X0))) ),
    inference(forward_demodulation,[],[f104,f33])).

fof(f104,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k6_relat_1(X0)),k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) ),
    inference(unit_resulting_resolution,[],[f31,f32,f44,f44,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(forward_demodulation,[],[f67,f33])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f31,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f1163,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f1148,f101])).

fof(f101,plain,
    ( ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f95,f82])).

fof(f82,plain,
    ( ! [X0] : k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f49,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f49,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f95,plain,
    ( ! [X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f31,f49,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f1148,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) = k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))
    | ~ spl3_14 ),
    inference(superposition,[],[f282,f322])).

fof(f322,plain,
    ( k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl3_14
  <=> k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f282,plain,(
    ! [X2,X1] : k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k10_relat_1(k6_relat_1(X2),X1) ),
    inference(superposition,[],[f100,f158])).

fof(f100,plain,(
    ! [X2,X0,X1] : k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_demodulation,[],[f97,f83])).

fof(f83,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unit_resulting_resolution,[],[f31,f37])).

fof(f97,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(unit_resulting_resolution,[],[f31,f31,f39])).

fof(f323,plain,
    ( spl3_14
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f203,f57,f320])).

fof(f57,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f203,plain,
    ( k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f59,f93])).

fof(f93,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f92,f83])).

fof(f92,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f89,f33])).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f38,f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f59,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f65,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f60,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f47])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:48:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (3672)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (3691)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.39/0.55  % (3670)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.39/0.56  % (3680)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.39/0.56  % (3673)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.39/0.56  % (3679)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.39/0.56  % (3674)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.39/0.56  % (3669)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.57  % (3673)Refutation not found, incomplete strategy% (3673)------------------------------
% 1.39/0.57  % (3673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (3673)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (3673)Memory used [KB]: 6140
% 1.39/0.57  % (3673)Time elapsed: 0.128 s
% 1.39/0.57  % (3673)------------------------------
% 1.39/0.57  % (3673)------------------------------
% 1.39/0.57  % (3674)Refutation not found, incomplete strategy% (3674)------------------------------
% 1.39/0.57  % (3674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (3674)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (3674)Memory used [KB]: 10618
% 1.39/0.57  % (3674)Time elapsed: 0.134 s
% 1.39/0.57  % (3674)------------------------------
% 1.39/0.57  % (3674)------------------------------
% 1.39/0.57  % (3679)Refutation not found, incomplete strategy% (3679)------------------------------
% 1.39/0.57  % (3679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (3679)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (3679)Memory used [KB]: 10618
% 1.39/0.57  % (3679)Time elapsed: 0.134 s
% 1.39/0.57  % (3679)------------------------------
% 1.39/0.57  % (3679)------------------------------
% 1.61/0.57  % (3681)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.61/0.57  % (3686)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.61/0.57  % (3689)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.61/0.57  % (3693)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.61/0.58  % (3678)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.61/0.58  % (3684)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.61/0.58  % (3691)Refutation found. Thanks to Tanya!
% 1.61/0.58  % SZS status Theorem for theBenchmark
% 1.61/0.58  % (3671)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.61/0.58  % (3683)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.61/0.58  % (3690)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.61/0.58  % (3676)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.61/0.58  % (3685)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.61/0.59  % (3669)Refutation not found, incomplete strategy% (3669)------------------------------
% 1.61/0.59  % (3669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (3669)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (3669)Memory used [KB]: 10618
% 1.61/0.59  % (3669)Time elapsed: 0.134 s
% 1.61/0.59  % (3669)------------------------------
% 1.61/0.59  % (3669)------------------------------
% 1.61/0.59  % SZS output start Proof for theBenchmark
% 1.61/0.59  fof(f1173,plain,(
% 1.61/0.59    $false),
% 1.61/0.59    inference(avatar_sat_refutation,[],[f50,f60,f65,f323,f1166])).
% 1.61/0.59  fof(f1166,plain,(
% 1.61/0.59    ~spl3_1 | spl3_4 | ~spl3_14),
% 1.61/0.59    inference(avatar_contradiction_clause,[],[f1165])).
% 1.61/0.59  fof(f1165,plain,(
% 1.61/0.59    $false | (~spl3_1 | spl3_4 | ~spl3_14)),
% 1.61/0.59    inference(subsumption_resolution,[],[f1164,f64])).
% 1.61/0.59  fof(f64,plain,(
% 1.61/0.59    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_4),
% 1.61/0.59    inference(avatar_component_clause,[],[f62])).
% 1.61/0.59  fof(f62,plain,(
% 1.61/0.59    spl3_4 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.61/0.59  fof(f1164,plain,(
% 1.61/0.59    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl3_1 | ~spl3_14)),
% 1.61/0.59    inference(forward_demodulation,[],[f1163,f158])).
% 1.61/0.59  fof(f158,plain,(
% 1.61/0.59    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f69,f108,f42])).
% 1.61/0.59  fof(f42,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.61/0.59    inference(cnf_transformation,[],[f26])).
% 1.61/0.59  fof(f26,plain,(
% 1.61/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.59    inference(flattening,[],[f25])).
% 1.61/0.59  fof(f25,plain,(
% 1.61/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.59    inference(nnf_transformation,[],[f1])).
% 1.61/0.59  fof(f1,axiom,(
% 1.61/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.61/0.59  fof(f108,plain,(
% 1.61/0.59    ( ! [X0] : (r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X0))) )),
% 1.61/0.59    inference(forward_demodulation,[],[f107,f75])).
% 1.61/0.59  fof(f75,plain,(
% 1.61/0.59    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.61/0.59    inference(forward_demodulation,[],[f74,f34])).
% 1.61/0.59  fof(f34,plain,(
% 1.61/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.61/0.59    inference(cnf_transformation,[],[f5])).
% 1.61/0.59  fof(f5,axiom,(
% 1.61/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.61/0.59  fof(f74,plain,(
% 1.61/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 1.61/0.59    inference(forward_demodulation,[],[f71,f33])).
% 1.61/0.59  fof(f33,plain,(
% 1.61/0.59    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.61/0.59    inference(cnf_transformation,[],[f5])).
% 1.61/0.59  fof(f71,plain,(
% 1.61/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f31,f35])).
% 1.61/0.59  fof(f35,plain,(
% 1.61/0.59    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f14])).
% 1.61/0.59  fof(f14,plain,(
% 1.61/0.59    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.59    inference(ennf_transformation,[],[f2])).
% 1.61/0.59  fof(f2,axiom,(
% 1.61/0.59    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.61/0.59  fof(f31,plain,(
% 1.61/0.59    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f8])).
% 1.61/0.59  fof(f8,axiom,(
% 1.61/0.59    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.61/0.59  fof(f107,plain,(
% 1.61/0.59    ( ! [X0] : (r1_tarski(X0,k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X0)))) )),
% 1.61/0.59    inference(forward_demodulation,[],[f104,f33])).
% 1.61/0.59  fof(f104,plain,(
% 1.61/0.59    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))))) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f31,f32,f44,f44,f43])).
% 1.61/0.59  fof(f43,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f21])).
% 1.61/0.59  fof(f21,plain,(
% 1.61/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.61/0.59    inference(flattening,[],[f20])).
% 1.61/0.59  fof(f20,plain,(
% 1.61/0.59    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.61/0.59    inference(ennf_transformation,[],[f9])).
% 1.61/0.59  fof(f9,axiom,(
% 1.61/0.59    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.61/0.59  fof(f44,plain,(
% 1.61/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.61/0.59    inference(equality_resolution,[],[f41])).
% 1.61/0.59  fof(f41,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.61/0.59    inference(cnf_transformation,[],[f26])).
% 1.61/0.59  fof(f32,plain,(
% 1.61/0.59    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f8])).
% 1.61/0.59  fof(f69,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.61/0.59    inference(forward_demodulation,[],[f67,f33])).
% 1.61/0.59  fof(f67,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0)))) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f31,f36])).
% 1.61/0.59  fof(f36,plain,(
% 1.61/0.59    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f15])).
% 1.61/0.59  fof(f15,plain,(
% 1.61/0.59    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f3])).
% 1.61/0.59  fof(f3,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.61/0.59  fof(f1163,plain,(
% 1.61/0.59    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) | (~spl3_1 | ~spl3_14)),
% 1.61/0.59    inference(forward_demodulation,[],[f1148,f101])).
% 1.61/0.59  fof(f101,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1)) ) | ~spl3_1),
% 1.61/0.59    inference(forward_demodulation,[],[f95,f82])).
% 1.61/0.59  fof(f82,plain,(
% 1.61/0.59    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),sK0) = k7_relat_1(sK0,X0)) ) | ~spl3_1),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f49,f37])).
% 1.61/0.59  fof(f37,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 1.61/0.59    inference(cnf_transformation,[],[f16])).
% 1.61/0.59  fof(f16,plain,(
% 1.61/0.59    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f7])).
% 1.61/0.59  fof(f7,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.61/0.59  fof(f49,plain,(
% 1.61/0.59    v1_relat_1(sK0) | ~spl3_1),
% 1.61/0.59    inference(avatar_component_clause,[],[f47])).
% 1.61/0.59  fof(f47,plain,(
% 1.61/0.59    spl3_1 <=> v1_relat_1(sK0)),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.61/0.59  fof(f95,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1))) ) | ~spl3_1),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f31,f49,f39])).
% 1.61/0.59  fof(f39,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) )),
% 1.61/0.59    inference(cnf_transformation,[],[f19])).
% 1.61/0.59  fof(f19,plain,(
% 1.61/0.59    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f4])).
% 1.61/0.59  fof(f4,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 1.61/0.59  fof(f1148,plain,(
% 1.61/0.59    k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) = k10_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) | ~spl3_14),
% 1.61/0.59    inference(superposition,[],[f282,f322])).
% 1.61/0.59  fof(f322,plain,(
% 1.61/0.59    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_14),
% 1.61/0.59    inference(avatar_component_clause,[],[f320])).
% 1.61/0.59  fof(f320,plain,(
% 1.61/0.59    spl3_14 <=> k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.61/0.59  fof(f282,plain,(
% 1.61/0.59    ( ! [X2,X1] : (k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X1) = k10_relat_1(k6_relat_1(X2),X1)) )),
% 1.61/0.59    inference(superposition,[],[f100,f158])).
% 1.61/0.59  fof(f100,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) )),
% 1.61/0.59    inference(forward_demodulation,[],[f97,f83])).
% 1.61/0.59  fof(f83,plain,(
% 1.61/0.59    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f31,f37])).
% 1.61/0.59  fof(f97,plain,(
% 1.61/0.59    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2))) )),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f31,f31,f39])).
% 1.61/0.59  fof(f323,plain,(
% 1.61/0.59    spl3_14 | ~spl3_3),
% 1.61/0.59    inference(avatar_split_clause,[],[f203,f57,f320])).
% 1.61/0.59  fof(f57,plain,(
% 1.61/0.59    spl3_3 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.61/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.61/0.59  fof(f203,plain,(
% 1.61/0.59    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~spl3_3),
% 1.61/0.59    inference(unit_resulting_resolution,[],[f59,f93])).
% 1.61/0.59  fof(f93,plain,(
% 1.61/0.59    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.61/0.59    inference(forward_demodulation,[],[f92,f83])).
% 1.61/0.59  fof(f92,plain,(
% 1.61/0.59    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 1.61/0.59    inference(forward_demodulation,[],[f89,f33])).
% 1.61/0.59  fof(f89,plain,(
% 1.61/0.59    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 1.61/0.59    inference(resolution,[],[f38,f31])).
% 1.61/0.59  fof(f38,plain,(
% 1.61/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 1.61/0.59    inference(cnf_transformation,[],[f18])).
% 1.61/0.59  fof(f18,plain,(
% 1.61/0.59    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(flattening,[],[f17])).
% 1.61/0.59  fof(f17,plain,(
% 1.61/0.59    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.61/0.59    inference(ennf_transformation,[],[f6])).
% 1.61/0.59  fof(f6,axiom,(
% 1.61/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 1.61/0.59  fof(f59,plain,(
% 1.61/0.59    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_3),
% 1.61/0.59    inference(avatar_component_clause,[],[f57])).
% 1.61/0.59  fof(f65,plain,(
% 1.61/0.59    ~spl3_4),
% 1.61/0.59    inference(avatar_split_clause,[],[f30,f62])).
% 1.61/0.59  fof(f30,plain,(
% 1.61/0.59    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.61/0.59    inference(cnf_transformation,[],[f24])).
% 1.61/0.59  fof(f24,plain,(
% 1.61/0.59    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.61/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f23,f22])).
% 1.61/0.59  fof(f22,plain,(
% 1.61/0.59    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.61/0.59    introduced(choice_axiom,[])).
% 1.61/0.59  fof(f23,plain,(
% 1.61/0.59    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.61/0.59    introduced(choice_axiom,[])).
% 1.61/0.59  fof(f13,plain,(
% 1.61/0.59    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.61/0.59    inference(flattening,[],[f12])).
% 1.61/0.59  fof(f12,plain,(
% 1.61/0.59    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.61/0.59    inference(ennf_transformation,[],[f11])).
% 1.61/0.59  fof(f11,negated_conjecture,(
% 1.61/0.59    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.61/0.59    inference(negated_conjecture,[],[f10])).
% 1.61/0.59  fof(f10,conjecture,(
% 1.61/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.61/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.61/0.59  fof(f60,plain,(
% 1.61/0.59    spl3_3),
% 1.61/0.59    inference(avatar_split_clause,[],[f29,f57])).
% 1.61/0.59  fof(f29,plain,(
% 1.61/0.59    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.61/0.59    inference(cnf_transformation,[],[f24])).
% 1.61/0.59  fof(f50,plain,(
% 1.61/0.59    spl3_1),
% 1.61/0.59    inference(avatar_split_clause,[],[f27,f47])).
% 1.61/0.59  fof(f27,plain,(
% 1.61/0.59    v1_relat_1(sK0)),
% 1.61/0.59    inference(cnf_transformation,[],[f24])).
% 1.61/0.59  % SZS output end Proof for theBenchmark
% 1.61/0.59  % (3691)------------------------------
% 1.61/0.59  % (3691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (3691)Termination reason: Refutation
% 1.61/0.59  
% 1.61/0.59  % (3691)Memory used [KB]: 11385
% 1.61/0.59  % (3691)Time elapsed: 0.140 s
% 1.61/0.59  % (3691)------------------------------
% 1.61/0.59  % (3691)------------------------------
% 1.61/0.59  % (3692)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.61/0.59  % (3667)Success in time 0.222 s
%------------------------------------------------------------------------------
