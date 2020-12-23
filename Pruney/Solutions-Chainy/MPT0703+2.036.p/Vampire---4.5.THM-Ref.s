%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 163 expanded)
%              Number of leaves         :   27 (  69 expanded)
%              Depth                    :    7
%              Number of atoms          :  240 ( 411 expanded)
%              Number of equality atoms :   30 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f853,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f108,f481,f525,f585,f671,f677,f707,f750,f775,f809,f852])).

fof(f852,plain,
    ( spl3_1
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f849,f767,f60])).

fof(f60,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f767,plain,
    ( spl3_43
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f849,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_43 ),
    inference(superposition,[],[f836,f86])).

fof(f86,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3 ),
    inference(resolution,[],[f45,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f836,plain,
    ( ! [X2] : r1_tarski(sK0,k2_xboole_0(X2,sK1))
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f826,f85])).

fof(f85,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(resolution,[],[f45,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f826,plain,
    ( ! [X2] : r1_tarski(k2_xboole_0(k3_xboole_0(sK0,X2),sK0),k2_xboole_0(X2,sK1))
    | ~ spl3_43 ),
    inference(superposition,[],[f52,f769])).

fof(f769,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f767])).

fof(f52,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f809,plain,(
    spl3_44 ),
    inference(avatar_contradiction_clause,[],[f802])).

fof(f802,plain,
    ( $false
    | spl3_44 ),
    inference(unit_resulting_resolution,[],[f42,f57,f773,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f773,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl3_44 ),
    inference(avatar_component_clause,[],[f771])).

fof(f771,plain,
    ( spl3_44
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f775,plain,
    ( spl3_43
    | ~ spl3_44
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f758,f747,f771,f767])).

fof(f747,plain,
    ( spl3_41
  <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f758,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_41 ),
    inference(resolution,[],[f749,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f749,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f747])).

fof(f750,plain,
    ( ~ spl3_5
    | ~ spl3_4
    | spl3_41
    | ~ spl3_31
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f745,f703,f668,f747,f75,f80])).

fof(f80,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f75,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f668,plain,
    ( spl3_31
  <=> sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f703,plain,
    ( spl3_35
  <=> k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f745,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_31
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f730,f670])).

fof(f670,plain,
    ( sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f668])).

fof(f730,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_35 ),
    inference(superposition,[],[f47,f705])).

fof(f705,plain,
    ( k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f703])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f707,plain,
    ( spl3_35
    | ~ spl3_26
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f699,f674,f582,f703])).

fof(f582,plain,
    ( spl3_26
  <=> r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f674,plain,
    ( spl3_32
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f699,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0))
    | k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl3_32 ),
    inference(resolution,[],[f676,f51])).

fof(f676,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f674])).

fof(f677,plain,
    ( spl3_32
    | ~ spl3_23
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f672,f668,f522,f674])).

fof(f522,plain,
    ( spl3_23
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f672,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_23
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f524,f670])).

fof(f524,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f522])).

fof(f671,plain,
    ( spl3_31
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f655,f479,f65,f668])).

fof(f65,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f479,plain,
    ( spl3_21
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f655,plain,
    ( sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(resolution,[],[f480,f67])).

fof(f67,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f480,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f479])).

fof(f585,plain,
    ( ~ spl3_5
    | spl3_26
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f569,f105,f582,f80])).

fof(f105,plain,
    ( spl3_8
  <=> k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f569,plain,
    ( r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f54,f107])).

fof(f107,plain,
    ( k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).

fof(f525,plain,
    ( ~ spl3_5
    | spl3_23
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f514,f105,f522,f80])).

fof(f514,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f53,f107])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_funct_1)).

fof(f481,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f477,f75,f80,f479])).

fof(f477,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_4 ),
    inference(resolution,[],[f48,f77])).

fof(f77,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f108,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f102,f70,f105])).

fof(f70,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f102,plain,
    ( k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f72])).

fof(f72,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f83,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f78,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f75])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f70])).

fof(f37,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f38,f65])).

fof(f38,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f39,f60])).

fof(f39,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (14773)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (14790)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (14783)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (14771)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (14782)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (14775)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (14787)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (14774)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (14792)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.50  % (14769)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (14785)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (14788)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (14779)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (14772)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (14777)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (14780)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (14781)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (14768)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (14789)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (14770)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (14791)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (14793)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (14784)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (14776)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (14786)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (14783)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f853,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f108,f481,f525,f585,f671,f677,f707,f750,f775,f809,f852])).
% 0.21/0.54  fof(f852,plain,(
% 0.21/0.54    spl3_1 | ~spl3_43),
% 0.21/0.54    inference(avatar_split_clause,[],[f849,f767,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f767,plain,(
% 0.21/0.54    spl3_43 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.54  fof(f849,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1) | ~spl3_43),
% 0.21/0.54    inference(superposition,[],[f836,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) )),
% 0.21/0.54    inference(resolution,[],[f45,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.54  fof(f836,plain,(
% 0.21/0.54    ( ! [X2] : (r1_tarski(sK0,k2_xboole_0(X2,sK1))) ) | ~spl3_43),
% 0.21/0.54    inference(forward_demodulation,[],[f826,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1) )),
% 0.21/0.54    inference(resolution,[],[f45,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.54  fof(f826,plain,(
% 0.21/0.54    ( ! [X2] : (r1_tarski(k2_xboole_0(k3_xboole_0(sK0,X2),sK0),k2_xboole_0(X2,sK1))) ) | ~spl3_43),
% 0.21/0.54    inference(superposition,[],[f52,f769])).
% 0.21/0.54  fof(f769,plain,(
% 0.21/0.54    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_43),
% 0.21/0.54    inference(avatar_component_clause,[],[f767])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.54  fof(f809,plain,(
% 0.21/0.54    spl3_44),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f802])).
% 0.21/0.54  fof(f802,plain,(
% 0.21/0.54    $false | spl3_44),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f42,f57,f773,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.54  fof(f773,plain,(
% 0.21/0.54    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl3_44),
% 0.21/0.54    inference(avatar_component_clause,[],[f771])).
% 0.21/0.54  fof(f771,plain,(
% 0.21/0.54    spl3_44 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f775,plain,(
% 0.21/0.54    spl3_43 | ~spl3_44 | ~spl3_41),
% 0.21/0.54    inference(avatar_split_clause,[],[f758,f747,f771,f767])).
% 0.21/0.54  fof(f747,plain,(
% 0.21/0.54    spl3_41 <=> r1_tarski(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.54  fof(f758,plain,(
% 0.21/0.54    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | sK0 = k3_xboole_0(sK0,sK1) | ~spl3_41),
% 0.21/0.54    inference(resolution,[],[f749,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f749,plain,(
% 0.21/0.54    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_41),
% 0.21/0.54    inference(avatar_component_clause,[],[f747])).
% 0.21/0.54  fof(f750,plain,(
% 0.21/0.54    ~spl3_5 | ~spl3_4 | spl3_41 | ~spl3_31 | ~spl3_35),
% 0.21/0.54    inference(avatar_split_clause,[],[f745,f703,f668,f747,f75,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl3_5 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl3_4 <=> v1_funct_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.54  fof(f668,plain,(
% 0.21/0.54    spl3_31 <=> sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.54  fof(f703,plain,(
% 0.21/0.54    spl3_35 <=> k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.54  fof(f745,plain,(
% 0.21/0.54    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_31 | ~spl3_35)),
% 0.21/0.54    inference(forward_demodulation,[],[f730,f670])).
% 0.21/0.54  fof(f670,plain,(
% 0.21/0.54    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | ~spl3_31),
% 0.21/0.54    inference(avatar_component_clause,[],[f668])).
% 0.21/0.54  fof(f730,plain,(
% 0.21/0.54    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK0,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_35),
% 0.21/0.54    inference(superposition,[],[f47,f705])).
% 0.21/0.54  fof(f705,plain,(
% 0.21/0.54    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) | ~spl3_35),
% 0.21/0.54    inference(avatar_component_clause,[],[f703])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.21/0.54  fof(f707,plain,(
% 0.21/0.54    spl3_35 | ~spl3_26 | ~spl3_32),
% 0.21/0.54    inference(avatar_split_clause,[],[f699,f674,f582,f703])).
% 0.21/0.54  fof(f582,plain,(
% 0.21/0.54    spl3_26 <=> r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.54  fof(f674,plain,(
% 0.21/0.54    spl3_32 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(sK0,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.54  fof(f699,plain,(
% 0.21/0.54    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) | k10_relat_1(sK2,sK0) = k10_relat_1(sK2,k3_xboole_0(sK0,sK1)) | ~spl3_32),
% 0.21/0.54    inference(resolution,[],[f676,f51])).
% 0.21/0.54  fof(f676,plain,(
% 0.21/0.54    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) | ~spl3_32),
% 0.21/0.54    inference(avatar_component_clause,[],[f674])).
% 0.21/0.54  fof(f677,plain,(
% 0.21/0.54    spl3_32 | ~spl3_23 | ~spl3_31),
% 0.21/0.54    inference(avatar_split_clause,[],[f672,f668,f522,f674])).
% 0.21/0.54  fof(f522,plain,(
% 0.21/0.54    spl3_23 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.54  fof(f672,plain,(
% 0.21/0.54    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(sK0,sK1))) | (~spl3_23 | ~spl3_31)),
% 0.21/0.54    inference(backward_demodulation,[],[f524,f670])).
% 0.21/0.54  fof(f524,plain,(
% 0.21/0.54    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1))) | ~spl3_23),
% 0.21/0.54    inference(avatar_component_clause,[],[f522])).
% 0.21/0.54  fof(f671,plain,(
% 0.21/0.54    spl3_31 | ~spl3_2 | ~spl3_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f655,f479,f65,f668])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    spl3_2 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f479,plain,(
% 0.21/0.54    spl3_21 <=> ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.55  fof(f655,plain,(
% 0.21/0.55    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | (~spl3_2 | ~spl3_21)),
% 0.21/0.55    inference(resolution,[],[f480,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f65])).
% 0.21/0.55  fof(f480,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | ~spl3_21),
% 0.21/0.55    inference(avatar_component_clause,[],[f479])).
% 0.21/0.55  fof(f585,plain,(
% 0.21/0.55    ~spl3_5 | spl3_26 | ~spl3_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f569,f105,f582,f80])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    spl3_8 <=> k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.55  fof(f569,plain,(
% 0.21/0.55    r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl3_8),
% 0.21/0.55    inference(superposition,[],[f54,f107])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f105])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).
% 0.21/0.55  fof(f525,plain,(
% 0.21/0.55    ~spl3_5 | spl3_23 | ~spl3_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f514,f105,f522,f80])).
% 0.21/0.55  fof(f514,plain,(
% 0.21/0.55    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1))) | ~v1_relat_1(sK2) | ~spl3_8),
% 0.21/0.55    inference(superposition,[],[f53,f107])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) | ~v1_relat_1(X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_funct_1)).
% 0.21/0.55  fof(f481,plain,(
% 0.21/0.55    spl3_21 | ~spl3_5 | ~spl3_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f477,f75,f80,f479])).
% 0.21/0.55  fof(f477,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(sK2) | ~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | ~spl3_4),
% 0.21/0.55    inference(resolution,[],[f48,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    v1_funct_1(sK2) | ~spl3_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f75])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    spl3_8 | ~spl3_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f102,f70,f105])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    spl3_3 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 0.21/0.55    inference(resolution,[],[f46,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f70])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    spl3_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f35,f80])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    v1_relat_1(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f16])).
% 0.21/0.55  fof(f16,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    spl3_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f36,f75])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    v1_funct_1(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    spl3_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f37,f70])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    spl3_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f38,f65])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ~spl3_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f39,f60])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ~r1_tarski(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (14783)------------------------------
% 0.21/0.55  % (14783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14783)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (14783)Memory used [KB]: 6780
% 0.21/0.55  % (14783)Time elapsed: 0.092 s
% 0.21/0.55  % (14783)------------------------------
% 0.21/0.55  % (14783)------------------------------
% 0.21/0.55  % (14767)Success in time 0.196 s
%------------------------------------------------------------------------------
