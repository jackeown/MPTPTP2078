%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 145 expanded)
%              Number of leaves         :   25 (  63 expanded)
%              Depth                    :    7
%              Number of atoms          :  290 ( 514 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f72,f92,f104,f112,f124,f129,f134,f144,f151,f154,f161,f167])).

fof(f167,plain,
    ( ~ spl5_18
    | ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl5_18
    | ~ spl5_24 ),
    inference(resolution,[],[f122,f160])).

fof(f160,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl5_24
  <=> ! [X2] : ~ r2_hidden(X2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f122,plain,
    ( r2_hidden(k1_funct_1(sK2,sK1),sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_18
  <=> r2_hidden(k1_funct_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f161,plain,
    ( spl5_24
    | ~ spl5_6
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f157,f117,f70,f159])).

fof(f70,plain,
    ( spl5_6
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f117,plain,
    ( spl5_17
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f157,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl5_6
    | ~ spl5_17 ),
    inference(resolution,[],[f119,f71])).

fof(f71,plain,
    ( ! [X2,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X2,X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f119,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f117])).

fof(f154,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_14
    | spl5_23 ),
    inference(avatar_split_clause,[],[f152,f148,f102,f55,f45])).

fof(f45,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f55,plain,
    ( spl5_3
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f102,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f148,plain,
    ( spl5_23
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f152,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl5_14
    | spl5_23 ),
    inference(resolution,[],[f150,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f150,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f148])).

fof(f151,plain,
    ( ~ spl5_23
    | ~ spl5_4
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f146,f142,f127,f60,f148])).

fof(f60,plain,
    ( spl5_4
  <=> r2_hidden(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f127,plain,
    ( spl5_19
  <=> ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK1),X0)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f142,plain,
    ( spl5_22
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f146,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl5_19
    | ~ spl5_22 ),
    inference(resolution,[],[f143,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK1),X0)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f127])).

fof(f143,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( ~ spl5_1
    | spl5_22
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f140,f132,f50,f142,f45])).

fof(f50,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f132,plain,
    ( spl5_20
  <=> ! [X1,X0] :
        ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl5_2
    | ~ spl5_20 ),
    inference(resolution,[],[f133,f52])).

fof(f52,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f40,f132])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f129,plain,
    ( spl5_19
    | ~ spl5_16
    | spl5_18 ),
    inference(avatar_split_clause,[],[f125,f121,f110,f127])).

fof(f110,plain,
    ( spl5_16
  <=> ! [X1,X3,X0] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK1),X0)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl5_16
    | spl5_18 ),
    inference(resolution,[],[f111,f123])).

fof(f123,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK1),sK0)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f121])).

fof(f111,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f124,plain,
    ( spl5_17
    | ~ spl5_18
    | spl5_5
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f113,f90,f65,f121,f117])).

fof(f65,plain,
    ( spl5_5
  <=> m1_subset_1(k1_funct_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f90,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f113,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK1),sK0)
    | v1_xboole_0(sK0)
    | spl5_5
    | ~ spl5_11 ),
    inference(resolution,[],[f91,f67])).

fof(f67,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f112,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f41,f110])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f104,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f38,f102])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f92,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f35,f90])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f72,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f68,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
    & r2_hidden(sK1,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
        & r2_hidden(X1,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
   => ( ~ m1_subset_1(k1_funct_1(sK2,sK1),sK0)
      & r2_hidden(sK1,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(k1_funct_1(X2,X1),X0)
      & r2_hidden(X1,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v5_relat_1(X2,X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(f63,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f27,f45])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.44  % (4132)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.47  % (4136)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (4144)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.20/0.48  % (4141)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.48  % (4144)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f72,f92,f104,f112,f124,f129,f134,f144,f151,f154,f161,f167])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    ~spl5_18 | ~spl5_24),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f166])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    $false | (~spl5_18 | ~spl5_24)),
% 0.20/0.48    inference(resolution,[],[f122,f160])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl5_24),
% 0.20/0.48    inference(avatar_component_clause,[],[f159])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    spl5_24 <=> ! [X2] : ~r2_hidden(X2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    r2_hidden(k1_funct_1(sK2,sK1),sK0) | ~spl5_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f121])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    spl5_18 <=> r2_hidden(k1_funct_1(sK2,sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    spl5_24 | ~spl5_6 | ~spl5_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f157,f117,f70,f159])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl5_6 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    spl5_17 <=> v1_xboole_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | (~spl5_6 | ~spl5_17)),
% 0.20/0.48    inference(resolution,[],[f119,f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) ) | ~spl5_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f70])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    v1_xboole_0(sK0) | ~spl5_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f117])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    ~spl5_1 | ~spl5_3 | ~spl5_14 | spl5_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f152,f148,f102,f55,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl5_1 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl5_3 <=> v5_relat_1(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl5_14 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    spl5_23 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | (~spl5_14 | spl5_23)),
% 0.20/0.48    inference(resolution,[],[f150,f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl5_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f102])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    ~r1_tarski(k2_relat_1(sK2),sK0) | spl5_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f148])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    ~spl5_23 | ~spl5_4 | ~spl5_19 | ~spl5_22),
% 0.20/0.48    inference(avatar_split_clause,[],[f146,f142,f127,f60,f148])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    spl5_4 <=> r2_hidden(sK1,k1_relat_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    spl5_19 <=> ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK1),X0) | ~r1_tarski(X0,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    spl5_22 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    ~r2_hidden(sK1,k1_relat_1(sK2)) | ~r1_tarski(k2_relat_1(sK2),sK0) | (~spl5_19 | ~spl5_22)),
% 0.20/0.48    inference(resolution,[],[f143,f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK1),X0) | ~r1_tarski(X0,sK0)) ) | ~spl5_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f127])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2))) ) | ~spl5_22),
% 0.20/0.48    inference(avatar_component_clause,[],[f142])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ~spl5_1 | spl5_22 | ~spl5_2 | ~spl5_20),
% 0.20/0.48    inference(avatar_split_clause,[],[f140,f132,f50,f142,f45])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    spl5_2 <=> v1_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    spl5_20 <=> ! [X1,X0] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | (~spl5_2 | ~spl5_20)),
% 0.20/0.48    inference(resolution,[],[f133,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    v1_funct_1(sK2) | ~spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f50])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl5_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f132])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    spl5_20),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f132])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    spl5_19 | ~spl5_16 | spl5_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f125,f121,f110,f127])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    spl5_16 <=> ! [X1,X3,X0] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK1),X0) | ~r1_tarski(X0,sK0)) ) | (~spl5_16 | spl5_18)),
% 0.20/0.48    inference(resolution,[],[f111,f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK2,sK1),sK0) | spl5_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f121])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) ) | ~spl5_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f110])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    spl5_17 | ~spl5_18 | spl5_5 | ~spl5_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f113,f90,f65,f121,f117])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl5_5 <=> m1_subset_1(k1_funct_1(sK2,sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl5_11 <=> ! [X1,X0] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK2,sK1),sK0) | v1_xboole_0(sK0) | (spl5_5 | ~spl5_11)),
% 0.20/0.48    inference(resolution,[],[f91,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ~m1_subset_1(k1_funct_1(sK2,sK1),sK0) | spl5_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f65])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) ) | ~spl5_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f90])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl5_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f110])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    spl5_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f38,f102])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl5_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f35,f90])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl5_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f70])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(rectify,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ~spl5_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f31,f65])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ~m1_subset_1(k1_funct_1(sK2,sK1),sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ~m1_subset_1(k1_funct_1(sK2,sK1),sK0) & r2_hidden(sK1,k1_relat_1(sK2)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (~m1_subset_1(k1_funct_1(sK2,sK1),sK0) & r2_hidden(sK1,k1_relat_1(sK2)) & v1_funct_1(sK2) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2)) & v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k1_funct_1(X2,X1),X0) & r2_hidden(X1,k1_relat_1(X2))) & (v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f30,f60])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    r2_hidden(sK1,k1_relat_1(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl5_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f55])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    v5_relat_1(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f50])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f45])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (4144)------------------------------
% 0.20/0.48  % (4144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (4144)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (4144)Memory used [KB]: 5373
% 0.20/0.48  % (4144)Time elapsed: 0.063 s
% 0.20/0.48  % (4144)------------------------------
% 0.20/0.48  % (4144)------------------------------
% 0.20/0.48  % (4127)Success in time 0.122 s
%------------------------------------------------------------------------------
