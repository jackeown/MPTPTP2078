%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 228 expanded)
%              Number of leaves         :   22 (  99 expanded)
%              Depth                    :    9
%              Number of atoms          :  398 (1137 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f56,f58,f62,f66,f74,f83,f112,f122,f129,f134,f142,f147,f162,f164,f187,f195,f209])).

fof(f209,plain,
    ( ~ spl4_5
    | ~ spl4_7
    | spl4_1
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f208,f160,f45,f72,f64])).

fof(f64,plain,
    ( spl4_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f72,plain,
    ( spl4_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f45,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f160,plain,
    ( spl4_18
  <=> r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f208,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f194,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f194,plain,
    ( r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f195,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f189,f183,f51,f160])).

fof(f51,plain,
    ( spl4_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f183,plain,
    ( spl4_21
  <=> ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),X0)
        | r2_hidden(sK0,k10_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f189,plain,
    ( r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1)))
    | ~ spl4_3
    | ~ spl4_21 ),
    inference(resolution,[],[f184,f55])).

fof(f55,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),X0)
        | r2_hidden(sK0,k10_relat_1(sK2,X0)) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f183])).

fof(f187,plain,
    ( ~ spl4_14
    | spl4_21
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f179,f120,f64,f183,f127])).

fof(f127,plain,
    ( spl4_14
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f120,plain,
    ( spl4_13
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f179,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK0),X1)
        | ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
        | r2_hidden(sK0,k10_relat_1(sK2,X1)) )
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(resolution,[],[f153,f121])).

fof(f121,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X0),sK2)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | r2_hidden(X2,k10_relat_1(sK2,X1)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f39,f65])).

fof(f65,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
            & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
        & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f164,plain,
    ( ~ spl4_5
    | ~ spl4_7
    | ~ spl4_1
    | spl4_18 ),
    inference(avatar_split_clause,[],[f163,f160,f45,f72,f64])).

fof(f163,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | spl4_18 ),
    inference(superposition,[],[f161,f33])).

fof(f161,plain,
    ( ~ r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( ~ spl4_5
    | ~ spl4_18
    | spl4_3
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f158,f140,f51,f160,f64])).

fof(f140,plain,
    ( spl4_16
  <=> k1_funct_1(sK2,sK0) = sK3(sK0,k1_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f158,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl4_16 ),
    inference(superposition,[],[f38,f141])).

fof(f141,plain,
    ( k1_funct_1(sK2,sK0) = sK3(sK0,k1_relat_1(sK1),sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f147,plain,
    ( ~ spl4_5
    | spl4_2
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f137,f132,f48,f64])).

fof(f48,plain,
    ( spl4_2
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f132,plain,
    ( spl4_15
  <=> r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f137,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(resolution,[],[f133,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f133,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f142,plain,
    ( ~ spl4_5
    | ~ spl4_4
    | spl4_16
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f135,f132,f140,f60,f64])).

fof(f60,plain,
    ( spl4_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f135,plain,
    ( k1_funct_1(sK2,sK0) = sK3(sK0,k1_relat_1(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(resolution,[],[f133,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f134,plain,
    ( spl4_15
    | ~ spl4_7
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f130,f81,f45,f72,f132])).

fof(f81,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,X0)))
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(X0),sK2)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f130,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2)
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(resolution,[],[f54,f82])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,X0)))
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(X0),sK2)),sK2) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f54,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f129,plain,
    ( ~ spl4_5
    | spl4_14
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f124,f120,f127,f64])).

fof(f124,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_13 ),
    inference(resolution,[],[f121,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f122,plain,
    ( spl4_13
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f117,f110,f48,f120])).

fof(f110,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f117,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(resolution,[],[f111,f57])).

fof(f57,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( ~ spl4_5
    | spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f107,f60,f110,f64])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_4 ),
    inference(resolution,[],[f43,f61])).

fof(f61,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

% (29283)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f83,plain,
    ( ~ spl4_5
    | spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f78,f64,f81,f64])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,X0)))
        | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(X0),sK2)),sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_5 ),
    inference(superposition,[],[f75,f33])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_relat_1(sK2,X1))
        | r2_hidden(k4_tarski(X0,sK3(X0,X1,sK2)),sK2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f37,f65])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f26,f72])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2))
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
            | ~ r2_hidden(sK0,k1_relat_1(X2))
            | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
          & ( ( r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
              & r2_hidden(sK0,k1_relat_1(X2)) )
            | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
          | ~ r2_hidden(sK0,k1_relat_1(X2))
          | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
        & ( ( r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
            & r2_hidden(sK0,k1_relat_1(X2)) )
          | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f66,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f30,f48,f45])).

fof(f30,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f31,f51,f45])).

fof(f31,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f32,f51,f48,f45])).

fof(f32,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:45:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (29288)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (29297)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (29289)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (29289)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (29296)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (29294)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f53,f56,f58,f62,f66,f74,f83,f112,f122,f129,f134,f142,f147,f162,f164,f187,f195,f209])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ~spl4_5 | ~spl4_7 | spl4_1 | ~spl4_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f208,f160,f45,f72,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl4_5 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl4_7 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl4_1 <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    spl4_18 <=> r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~spl4_18),
% 0.21/0.49    inference(superposition,[],[f194,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1))) | ~spl4_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f160])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    spl4_18 | ~spl4_3 | ~spl4_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f189,f183,f51,f160])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl4_3 <=> r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    spl4_21 <=> ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK0),X0) | r2_hidden(sK0,k10_relat_1(sK2,X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1))) | (~spl4_3 | ~spl4_21)),
% 0.21/0.49    inference(resolution,[],[f184,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK0),X0) | r2_hidden(sK0,k10_relat_1(sK2,X0))) ) | ~spl4_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f183])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ~spl4_14 | spl4_21 | ~spl4_5 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f179,f120,f64,f183,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl4_14 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl4_13 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(k1_funct_1(sK2,sK0),X1) | ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | r2_hidden(sK0,k10_relat_1(sK2,X1))) ) | (~spl4_5 | ~spl4_13)),
% 0.21/0.49    inference(resolution,[],[f153,f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X0),sK2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X2,k10_relat_1(sK2,X1))) ) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f39,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f64])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) & r2_hidden(sK3(X0,X1,X2),k2_relat_1(X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(rectify,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ~spl4_5 | ~spl4_7 | ~spl4_1 | spl4_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f163,f160,f45,f72,f64])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | spl4_18),
% 0.21/0.49    inference(superposition,[],[f161,f33])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1))) | spl4_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f160])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~spl4_5 | ~spl4_18 | spl4_3 | ~spl4_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f158,f140,f51,f160,f64])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl4_16 <=> k1_funct_1(sK2,sK0) = sK3(sK0,k1_relat_1(sK1),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k10_relat_1(sK2,k1_relat_1(sK1))) | ~v1_relat_1(sK2) | ~spl4_16),
% 0.21/0.49    inference(superposition,[],[f38,f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    k1_funct_1(sK2,sK0) = sK3(sK0,k1_relat_1(sK1),sK2) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~spl4_5 | spl4_2 | ~spl4_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f137,f132,f48,f64])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl4_2 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl4_15 <=> r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_15),
% 0.21/0.49    inference(resolution,[],[f133,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2) | ~spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f132])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ~spl4_5 | ~spl4_4 | spl4_16 | ~spl4_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f135,f132,f140,f60,f64])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl4_4 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    k1_funct_1(sK2,sK0) = sK3(sK0,k1_relat_1(sK1),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_15),
% 0.21/0.49    inference(resolution,[],[f133,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl4_15 | ~spl4_7 | ~spl4_1 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f130,f81,f45,f72,f132])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl4_8 <=> ! [X1,X0] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,X0))) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(X0),sK2)),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK0,sK3(sK0,k1_relat_1(sK1),sK2)),sK2) | (~spl4_1 | ~spl4_8)),
% 0.21/0.49    inference(resolution,[],[f54,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,X0))) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(X0),sK2)),sK2)) ) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) | ~spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~spl4_5 | spl4_14 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f124,f120,f127,f64])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_13),
% 0.21/0.49    inference(resolution,[],[f121,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl4_13 | ~spl4_2 | ~spl4_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f117,f110,f48,f120])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl4_11 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | (~spl4_2 | ~spl4_11)),
% 0.21/0.49    inference(resolution,[],[f111,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f48])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)) ) | ~spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f110])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ~spl4_5 | spl4_11 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f107,f60,f110,f64])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~v1_relat_1(sK2)) ) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f43,f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    v1_funct_1(sK2) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(equality_resolution,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  % (29283)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~spl4_5 | spl4_8 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f78,f64,f81,f64])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,X0))) | r2_hidden(k4_tarski(X1,sK3(X1,k1_relat_1(X0),sK2)),sK2) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) ) | ~spl4_5),
% 0.21/0.49    inference(superposition,[],[f75,f33])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK2,X1)) | r2_hidden(k4_tarski(X0,sK3(X0,X1,sK2)),sK2)) ) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f37,f65])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f72])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ((~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & ((r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(X2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & ((r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(X2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X2] : ((~r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(X2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & ((r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(X2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1)))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & ((r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((((~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <~> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f64])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f60])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl4_1 | spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f48,f45])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl4_1 | spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f51,f45])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f51,f48,f45])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (29289)------------------------------
% 0.21/0.49  % (29289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29289)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (29289)Memory used [KB]: 10874
% 0.21/0.49  % (29289)Time elapsed: 0.063 s
% 0.21/0.49  % (29289)------------------------------
% 0.21/0.49  % (29289)------------------------------
% 0.21/0.50  % (29295)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (29282)Success in time 0.135 s
%------------------------------------------------------------------------------
