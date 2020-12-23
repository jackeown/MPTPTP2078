%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 161 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  274 ( 505 expanded)
%              Number of equality atoms :   48 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f830,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f58,f63,f67,f71,f105,f146,f169,f185,f258,f285,f365,f678,f820,f829])).

fof(f829,plain,
    ( ~ spl3_1
    | spl3_13
    | ~ spl3_23
    | ~ spl3_37
    | ~ spl3_73 ),
    inference(avatar_contradiction_clause,[],[f828])).

fof(f828,plain,
    ( $false
    | ~ spl3_1
    | spl3_13
    | ~ spl3_23
    | ~ spl3_37
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f827,f38])).

fof(f38,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f827,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_13
    | ~ spl3_23
    | ~ spl3_37
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f826,f104])).

fof(f104,plain,
    ( k1_xboole_0 != k6_subset_1(sK0,sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl3_13
  <=> k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f826,plain,
    ( k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_23
    | ~ spl3_37
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f824,f284])).

fof(f284,plain,
    ( ! [X15] : r1_tarski(k6_subset_1(sK0,X15),k2_relat_1(sK2))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl3_37
  <=> ! [X15] : r1_tarski(k6_subset_1(sK0,X15),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f824,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_23
    | ~ spl3_73 ),
    inference(trivial_inequality_removal,[],[f823])).

fof(f823,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2))
    | k1_xboole_0 = k6_subset_1(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_23
    | ~ spl3_73 ),
    inference(superposition,[],[f184,f819])).

fof(f819,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f817])).

fof(f817,plain,
    ( spl3_73
  <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k10_relat_1(X1,X0)
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X1) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k10_relat_1(X1,X0)
        | ~ r1_tarski(X0,k2_relat_1(X1))
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f820,plain,
    ( spl3_73
    | ~ spl3_18
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f802,f676,f143,f817])).

fof(f143,plain,
    ( spl3_18
  <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f676,plain,
    ( spl3_66
  <=> ! [X1,X0] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f802,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))
    | ~ spl3_18
    | ~ spl3_66 ),
    inference(superposition,[],[f677,f145])).

fof(f145,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f677,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f676])).

fof(f678,plain,
    ( spl3_66
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f512,f363,f41,f36,f676])).

fof(f41,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f363,plain,
    ( spl3_44
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f512,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f511,f38])).

fof(f511,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_2
    | ~ spl3_44 ),
    inference(resolution,[],[f364,f43])).

fof(f43,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f364,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f363])).

fof(f365,plain,(
    spl3_44 ),
    inference(avatar_split_clause,[],[f30,f363])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f285,plain,
    ( spl3_37
    | ~ spl3_4
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f268,f256,f51,f283])).

fof(f51,plain,
    ( spl3_4
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f256,plain,
    ( spl3_35
  <=> ! [X9,X11,X10] :
        ( ~ r1_tarski(X9,X10)
        | r1_tarski(k6_subset_1(X9,X11),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f268,plain,
    ( ! [X15] : r1_tarski(k6_subset_1(sK0,X15),k2_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_35 ),
    inference(resolution,[],[f257,f53])).

fof(f53,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f257,plain,
    ( ! [X10,X11,X9] :
        ( ~ r1_tarski(X9,X10)
        | r1_tarski(k6_subset_1(X9,X11),X10) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( spl3_35
    | ~ spl3_5
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f175,f167,f56,f256])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f167,plain,
    ( spl3_21
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f175,plain,
    ( ! [X10,X11,X9] :
        ( ~ r1_tarski(X9,X10)
        | r1_tarski(k6_subset_1(X9,X11),X10) )
    | ~ spl3_5
    | ~ spl3_21 ),
    inference(resolution,[],[f168,f57])).

fof(f57,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f167])).

fof(f185,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f27,f183])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f169,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f31,f167])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f146,plain,
    ( spl3_18
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f74,f65,f60,f143])).

fof(f60,plain,
    ( spl3_6
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f65,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k6_subset_1(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f66,f62])).

fof(f62,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k6_subset_1(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f105,plain,
    ( ~ spl3_13
    | spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f98,f69,f46,f102])).

fof(f46,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f69,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f98,plain,
    ( k1_xboole_0 != k6_subset_1(sK0,sK1)
    | spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k6_subset_1(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f67,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f65])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f60])).

fof(f22,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(f58,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f32,f56])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:28:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (17839)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.43  % (17839)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f830,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f58,f63,f67,f71,f105,f146,f169,f185,f258,f285,f365,f678,f820,f829])).
% 0.22/0.43  fof(f829,plain,(
% 0.22/0.43    ~spl3_1 | spl3_13 | ~spl3_23 | ~spl3_37 | ~spl3_73),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f828])).
% 0.22/0.43  fof(f828,plain,(
% 0.22/0.43    $false | (~spl3_1 | spl3_13 | ~spl3_23 | ~spl3_37 | ~spl3_73)),
% 0.22/0.43    inference(subsumption_resolution,[],[f827,f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.43  fof(f827,plain,(
% 0.22/0.43    ~v1_relat_1(sK2) | (spl3_13 | ~spl3_23 | ~spl3_37 | ~spl3_73)),
% 0.22/0.43    inference(subsumption_resolution,[],[f826,f104])).
% 0.22/0.43  fof(f104,plain,(
% 0.22/0.43    k1_xboole_0 != k6_subset_1(sK0,sK1) | spl3_13),
% 0.22/0.43    inference(avatar_component_clause,[],[f102])).
% 0.22/0.43  fof(f102,plain,(
% 0.22/0.43    spl3_13 <=> k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.43  fof(f826,plain,(
% 0.22/0.43    k1_xboole_0 = k6_subset_1(sK0,sK1) | ~v1_relat_1(sK2) | (~spl3_23 | ~spl3_37 | ~spl3_73)),
% 0.22/0.43    inference(subsumption_resolution,[],[f824,f284])).
% 0.22/0.43  fof(f284,plain,(
% 0.22/0.43    ( ! [X15] : (r1_tarski(k6_subset_1(sK0,X15),k2_relat_1(sK2))) ) | ~spl3_37),
% 0.22/0.43    inference(avatar_component_clause,[],[f283])).
% 0.22/0.43  fof(f283,plain,(
% 0.22/0.43    spl3_37 <=> ! [X15] : r1_tarski(k6_subset_1(sK0,X15),k2_relat_1(sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.43  fof(f824,plain,(
% 0.22/0.43    ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | k1_xboole_0 = k6_subset_1(sK0,sK1) | ~v1_relat_1(sK2) | (~spl3_23 | ~spl3_73)),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f823])).
% 0.22/0.43  fof(f823,plain,(
% 0.22/0.43    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) | k1_xboole_0 = k6_subset_1(sK0,sK1) | ~v1_relat_1(sK2) | (~spl3_23 | ~spl3_73)),
% 0.22/0.43    inference(superposition,[],[f184,f819])).
% 0.22/0.43  fof(f819,plain,(
% 0.22/0.43    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | ~spl3_73),
% 0.22/0.43    inference(avatar_component_clause,[],[f817])).
% 0.22/0.43  fof(f817,plain,(
% 0.22/0.43    spl3_73 <=> k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.22/0.43  fof(f184,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) ) | ~spl3_23),
% 0.22/0.43    inference(avatar_component_clause,[],[f183])).
% 0.22/0.43  fof(f183,plain,(
% 0.22/0.43    spl3_23 <=> ! [X1,X0] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.43  fof(f820,plain,(
% 0.22/0.43    spl3_73 | ~spl3_18 | ~spl3_66),
% 0.22/0.43    inference(avatar_split_clause,[],[f802,f676,f143,f817])).
% 0.22/0.43  fof(f143,plain,(
% 0.22/0.43    spl3_18 <=> k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.43  fof(f676,plain,(
% 0.22/0.43    spl3_66 <=> ! [X1,X0] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.22/0.43  fof(f802,plain,(
% 0.22/0.43    k1_xboole_0 = k10_relat_1(sK2,k6_subset_1(sK0,sK1)) | (~spl3_18 | ~spl3_66)),
% 0.22/0.43    inference(superposition,[],[f677,f145])).
% 0.22/0.43  fof(f145,plain,(
% 0.22/0.43    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_18),
% 0.22/0.43    inference(avatar_component_clause,[],[f143])).
% 0.22/0.43  fof(f677,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl3_66),
% 0.22/0.43    inference(avatar_component_clause,[],[f676])).
% 0.22/0.43  fof(f678,plain,(
% 0.22/0.43    spl3_66 | ~spl3_1 | ~spl3_2 | ~spl3_44),
% 0.22/0.43    inference(avatar_split_clause,[],[f512,f363,f41,f36,f676])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    spl3_2 <=> v1_funct_1(sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f363,plain,(
% 0.22/0.43    spl3_44 <=> ! [X1,X0,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.43  fof(f512,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | (~spl3_1 | ~spl3_2 | ~spl3_44)),
% 0.22/0.43    inference(subsumption_resolution,[],[f511,f38])).
% 0.22/0.43  fof(f511,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) ) | (~spl3_2 | ~spl3_44)),
% 0.22/0.43    inference(resolution,[],[f364,f43])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    v1_funct_1(sK2) | ~spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f41])).
% 0.22/0.43  fof(f364,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl3_44),
% 0.22/0.43    inference(avatar_component_clause,[],[f363])).
% 0.22/0.43  fof(f365,plain,(
% 0.22/0.43    spl3_44),
% 0.22/0.43    inference(avatar_split_clause,[],[f30,f363])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 0.22/0.43  fof(f285,plain,(
% 0.22/0.43    spl3_37 | ~spl3_4 | ~spl3_35),
% 0.22/0.43    inference(avatar_split_clause,[],[f268,f256,f51,f283])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    spl3_4 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.43  fof(f256,plain,(
% 0.22/0.43    spl3_35 <=> ! [X9,X11,X10] : (~r1_tarski(X9,X10) | r1_tarski(k6_subset_1(X9,X11),X10))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.43  fof(f268,plain,(
% 0.22/0.43    ( ! [X15] : (r1_tarski(k6_subset_1(sK0,X15),k2_relat_1(sK2))) ) | (~spl3_4 | ~spl3_35)),
% 0.22/0.43    inference(resolution,[],[f257,f53])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f51])).
% 0.22/0.43  fof(f257,plain,(
% 0.22/0.43    ( ! [X10,X11,X9] : (~r1_tarski(X9,X10) | r1_tarski(k6_subset_1(X9,X11),X10)) ) | ~spl3_35),
% 0.22/0.43    inference(avatar_component_clause,[],[f256])).
% 0.22/0.43  fof(f258,plain,(
% 0.22/0.43    spl3_35 | ~spl3_5 | ~spl3_21),
% 0.22/0.43    inference(avatar_split_clause,[],[f175,f167,f56,f256])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl3_5 <=> ! [X1,X0] : r1_tarski(k6_subset_1(X0,X1),X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.43  fof(f167,plain,(
% 0.22/0.43    spl3_21 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.43  fof(f175,plain,(
% 0.22/0.43    ( ! [X10,X11,X9] : (~r1_tarski(X9,X10) | r1_tarski(k6_subset_1(X9,X11),X10)) ) | (~spl3_5 | ~spl3_21)),
% 0.22/0.43    inference(resolution,[],[f168,f57])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) ) | ~spl3_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f56])).
% 0.22/0.43  fof(f168,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl3_21),
% 0.22/0.43    inference(avatar_component_clause,[],[f167])).
% 0.22/0.43  fof(f185,plain,(
% 0.22/0.43    spl3_23),
% 0.22/0.43    inference(avatar_split_clause,[],[f27,f183])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 0.22/0.43  fof(f169,plain,(
% 0.22/0.43    spl3_21),
% 0.22/0.43    inference(avatar_split_clause,[],[f31,f167])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(flattening,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.43  fof(f146,plain,(
% 0.22/0.43    spl3_18 | ~spl3_6 | ~spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f74,f65,f60,f143])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    spl3_6 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    spl3_7 <=> ! [X1,X0] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    k1_xboole_0 = k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | (~spl3_6 | ~spl3_7)),
% 0.22/0.43    inference(resolution,[],[f66,f62])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | ~spl3_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f60])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) ) | ~spl3_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f65])).
% 0.22/0.43  fof(f105,plain,(
% 0.22/0.43    ~spl3_13 | spl3_3 | ~spl3_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f98,f69,f46,f102])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    spl3_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    k1_xboole_0 != k6_subset_1(sK0,sK1) | (spl3_3 | ~spl3_8)),
% 0.22/0.43    inference(resolution,[],[f70,f48])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ~r1_tarski(sK0,sK1) | spl3_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f46])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) ) | ~spl3_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f69])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    spl3_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f34,f69])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f28,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.43    inference(nnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    spl3_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f33,f65])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f29,f26])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f60])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.44    inference(negated_conjecture,[],[f7])).
% 0.22/0.44  fof(f7,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f32,f56])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f25,f26])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f23,f51])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ~spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f24,f46])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ~r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f41])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    v1_funct_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f20,f36])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    v1_relat_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (17839)------------------------------
% 0.22/0.44  % (17839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (17839)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (17839)Memory used [KB]: 6524
% 0.22/0.44  % (17839)Time elapsed: 0.018 s
% 0.22/0.44  % (17839)------------------------------
% 0.22/0.44  % (17839)------------------------------
% 0.22/0.44  % (17831)Success in time 0.071 s
%------------------------------------------------------------------------------
