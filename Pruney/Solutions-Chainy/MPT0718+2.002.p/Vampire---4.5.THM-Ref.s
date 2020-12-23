%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 182 expanded)
%              Number of leaves         :   23 (  75 expanded)
%              Depth                    :    8
%              Number of atoms          :  422 ( 923 expanded)
%              Number of equality atoms :   12 (  68 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f76,f80,f84,f100,f108,f113,f122,f139,f146])).

fof(f146,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f45,plain,
    ( ~ v2_relat_1(sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl5_1
  <=> v2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f144,plain,
    ( v2_relat_1(sK1)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f143,f65])).

fof(f65,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f143,plain,
    ( ~ v1_relat_1(sK1)
    | v2_relat_1(sK1)
    | ~ spl5_4
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f142,f60])).

fof(f60,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f142,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_relat_1(sK1)
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f141,f121])).

fof(f121,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_17
  <=> r2_hidden(sK2(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f141,plain,
    ( ~ r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_relat_1(sK1)
    | ~ spl5_16
    | ~ spl5_19 ),
    inference(resolution,[],[f138,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_funct_1(X0,sK2(X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | v2_relat_1(X0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( v2_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_funct_1(X0,sK2(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f138,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_19
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f139,plain,
    ( spl5_19
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f135,f98,f73,f68,f63,f58,f53,f137])).

fof(f53,plain,
    ( spl5_3
  <=> v5_funct_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f68,plain,
    ( spl5_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f73,plain,
    ( spl5_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f98,plain,
    ( spl5_13
  <=> ! [X1,X3,X0] :
        ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
        | ~ r2_hidden(X3,k1_relat_1(X1))
        | ~ v5_funct_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0)) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f134,f65])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f133,f60])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f132,f75])).

fof(f75,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0))
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f131,f70])).

fof(f70,plain,
    ( v1_funct_1(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_3
    | ~ spl5_13 ),
    inference(resolution,[],[f99,f55])).

fof(f55,plain,
    ( v5_funct_1(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f99,plain,
    ( ! [X0,X3,X1] :
        ( ~ v5_funct_1(X1,X0)
        | ~ r2_hidden(X3,k1_relat_1(X1))
        | r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f122,plain,
    ( spl5_17
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f117,f82,f63,f58,f48,f43,f119])).

fof(f48,plain,
    ( spl5_2
  <=> k1_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f82,plain,
    ( spl5_9
  <=> ! [X0] :
        ( v2_relat_1(X0)
        | r2_hidden(sK2(X0),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f117,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f116,f65])).

fof(f116,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f115,f60])).

fof(f115,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f114,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | v2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(superposition,[],[f83,f50])).

fof(f50,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f83,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),k1_relat_1(X0))
        | v2_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f113,plain,
    ( spl5_16
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f109,f106,f78,f111])).

fof(f78,plain,
    ( spl5_8
  <=> ! [X0] :
        ( v2_relat_1(X0)
        | v1_xboole_0(k1_funct_1(X0,sK2(X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f106,plain,
    ( spl5_15
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( v2_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_funct_1(X0,sK2(X0))) )
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(resolution,[],[f79,f107])).

fof(f107,plain,
    ( ! [X2,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X2,X0) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f106])).

fof(f79,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
        | v2_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f108,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f40,f106])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
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

fof(f100,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f37,f98])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(f84,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f35,f82])).

fof(f35,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(k1_funct_1(X0,X1))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X1))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

fof(f80,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f36,f78])).

fof(f36,plain,(
    ! [X0] :
      ( v2_relat_1(X0)
      | v1_xboole_0(k1_funct_1(X0,sK2(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f27,f73])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v2_relat_1(sK1)
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v5_funct_1(sK0,sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_relat_1(X1)
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v5_funct_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(sK0)
          & v5_funct_1(sK0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ~ v2_relat_1(X1)
        & k1_relat_1(X1) = k1_relat_1(sK0)
        & v5_funct_1(sK0,X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_relat_1(sK1)
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v5_funct_1(sK0,sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k1_relat_1(X1)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k1_relat_1(X1)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

fof(f71,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f30,f58])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    v5_funct_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f32,f48])).

fof(f32,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f33,f43])).

fof(f33,plain,(
    ~ v2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:07:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (23834)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.44  % (23830)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.45  % (23830)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f147,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f46,f51,f56,f61,f66,f71,f76,f80,f84,f100,f108,f113,f122,f139,f146])).
% 0.22/0.45  fof(f146,plain,(
% 0.22/0.45    spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_16 | ~spl5_17 | ~spl5_19),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f145])).
% 0.22/0.45  fof(f145,plain,(
% 0.22/0.45    $false | (spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_16 | ~spl5_17 | ~spl5_19)),
% 0.22/0.45    inference(subsumption_resolution,[],[f144,f45])).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ~v2_relat_1(sK1) | spl5_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f43])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    spl5_1 <=> v2_relat_1(sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.45  fof(f144,plain,(
% 0.22/0.45    v2_relat_1(sK1) | (~spl5_4 | ~spl5_5 | ~spl5_16 | ~spl5_17 | ~spl5_19)),
% 0.22/0.45    inference(subsumption_resolution,[],[f143,f65])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    v1_relat_1(sK1) | ~spl5_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f63])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    spl5_5 <=> v1_relat_1(sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.45  fof(f143,plain,(
% 0.22/0.45    ~v1_relat_1(sK1) | v2_relat_1(sK1) | (~spl5_4 | ~spl5_16 | ~spl5_17 | ~spl5_19)),
% 0.22/0.45    inference(subsumption_resolution,[],[f142,f60])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    v1_funct_1(sK1) | ~spl5_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f58])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    spl5_4 <=> v1_funct_1(sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.45  fof(f142,plain,(
% 0.22/0.45    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | v2_relat_1(sK1) | (~spl5_16 | ~spl5_17 | ~spl5_19)),
% 0.22/0.45    inference(subsumption_resolution,[],[f141,f121])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | ~spl5_17),
% 0.22/0.45    inference(avatar_component_clause,[],[f119])).
% 0.22/0.45  fof(f119,plain,(
% 0.22/0.45    spl5_17 <=> r2_hidden(sK2(sK1),k1_relat_1(sK0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.45  fof(f141,plain,(
% 0.22/0.45    ~r2_hidden(sK2(sK1),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | v2_relat_1(sK1) | (~spl5_16 | ~spl5_19)),
% 0.22/0.45    inference(resolution,[],[f138,f112])).
% 0.22/0.45  fof(f112,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r2_hidden(X1,k1_funct_1(X0,sK2(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_relat_1(X0)) ) | ~spl5_16),
% 0.22/0.45    inference(avatar_component_clause,[],[f111])).
% 0.22/0.45  fof(f111,plain,(
% 0.22/0.45    spl5_16 <=> ! [X1,X0] : (v2_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_funct_1(X0,sK2(X0))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.45  fof(f138,plain,(
% 0.22/0.45    ( ! [X0] : (r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK0))) ) | ~spl5_19),
% 0.22/0.45    inference(avatar_component_clause,[],[f137])).
% 0.22/0.45  fof(f137,plain,(
% 0.22/0.45    spl5_19 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.45  fof(f139,plain,(
% 0.22/0.45    spl5_19 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f135,f98,f73,f68,f63,f58,f53,f137])).
% 0.22/0.45  fof(f53,plain,(
% 0.22/0.45    spl5_3 <=> v5_funct_1(sK0,sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    spl5_6 <=> v1_funct_1(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    spl5_7 <=> v1_relat_1(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.45  fof(f98,plain,(
% 0.22/0.45    spl5_13 <=> ! [X1,X3,X0] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.45  fof(f135,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0))) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_13)),
% 0.22/0.45    inference(subsumption_resolution,[],[f134,f65])).
% 0.22/0.45  fof(f134,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0)) | ~v1_relat_1(sK1)) ) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_13)),
% 0.22/0.45    inference(subsumption_resolution,[],[f133,f60])).
% 0.22/0.45  fof(f133,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_13)),
% 0.22/0.45    inference(subsumption_resolution,[],[f132,f75])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    v1_relat_1(sK0) | ~spl5_7),
% 0.22/0.45    inference(avatar_component_clause,[],[f73])).
% 0.22/0.45  fof(f132,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl5_3 | ~spl5_6 | ~spl5_13)),
% 0.22/0.45    inference(subsumption_resolution,[],[f131,f70])).
% 0.22/0.45  fof(f70,plain,(
% 0.22/0.45    v1_funct_1(sK0) | ~spl5_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f68])).
% 0.22/0.45  fof(f131,plain,(
% 0.22/0.45    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | r2_hidden(k1_funct_1(sK0,X0),k1_funct_1(sK1,X0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl5_3 | ~spl5_13)),
% 0.22/0.45    inference(resolution,[],[f99,f55])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    v5_funct_1(sK0,sK1) | ~spl5_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f53])).
% 0.22/0.45  fof(f99,plain,(
% 0.22/0.45    ( ! [X0,X3,X1] : (~v5_funct_1(X1,X0) | ~r2_hidden(X3,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_13),
% 0.22/0.45    inference(avatar_component_clause,[],[f98])).
% 0.22/0.45  fof(f122,plain,(
% 0.22/0.45    spl5_17 | spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f117,f82,f63,f58,f48,f43,f119])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    spl5_2 <=> k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.45  fof(f82,plain,(
% 0.22/0.45    spl5_9 <=> ! [X0] : (v2_relat_1(X0) | r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.45  fof(f117,plain,(
% 0.22/0.45    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_5 | ~spl5_9)),
% 0.22/0.45    inference(subsumption_resolution,[],[f116,f65])).
% 0.22/0.45  fof(f116,plain,(
% 0.22/0.45    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | ~v1_relat_1(sK1) | (spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_9)),
% 0.22/0.45    inference(subsumption_resolution,[],[f115,f60])).
% 0.22/0.45  fof(f115,plain,(
% 0.22/0.45    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl5_1 | ~spl5_2 | ~spl5_9)),
% 0.22/0.45    inference(subsumption_resolution,[],[f114,f45])).
% 0.22/0.45  fof(f114,plain,(
% 0.22/0.45    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | v2_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl5_2 | ~spl5_9)),
% 0.22/0.45    inference(superposition,[],[f83,f50])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    k1_relat_1(sK0) = k1_relat_1(sK1) | ~spl5_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f48])).
% 0.22/0.45  fof(f83,plain,(
% 0.22/0.45    ( ! [X0] : (r2_hidden(sK2(X0),k1_relat_1(X0)) | v2_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_9),
% 0.22/0.45    inference(avatar_component_clause,[],[f82])).
% 0.22/0.45  fof(f113,plain,(
% 0.22/0.45    spl5_16 | ~spl5_8 | ~spl5_15),
% 0.22/0.45    inference(avatar_split_clause,[],[f109,f106,f78,f111])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    spl5_8 <=> ! [X0] : (v2_relat_1(X0) | v1_xboole_0(k1_funct_1(X0,sK2(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.45  fof(f106,plain,(
% 0.22/0.45    spl5_15 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.45  fof(f109,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v2_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_funct_1(X0,sK2(X0)))) ) | (~spl5_8 | ~spl5_15)),
% 0.22/0.45    inference(resolution,[],[f79,f107])).
% 0.22/0.45  fof(f107,plain,(
% 0.22/0.45    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) ) | ~spl5_15),
% 0.22/0.45    inference(avatar_component_clause,[],[f106])).
% 0.22/0.45  fof(f79,plain,(
% 0.22/0.45    ( ! [X0] : (v1_xboole_0(k1_funct_1(X0,sK2(X0))) | v2_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_8),
% 0.22/0.45    inference(avatar_component_clause,[],[f78])).
% 0.22/0.45  fof(f108,plain,(
% 0.22/0.45    spl5_15),
% 0.22/0.45    inference(avatar_split_clause,[],[f40,f106])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.45    inference(rectify,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.45    inference(nnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    spl5_13),
% 0.22/0.45    inference(avatar_split_clause,[],[f37,f98])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X0,X3,X1] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1))) & r2_hidden(sK3(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1))) & r2_hidden(sK3(X0,X1),k1_relat_1(X1))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(rectify,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    spl5_9),
% 0.22/0.45    inference(avatar_split_clause,[],[f35,f82])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ( ! [X0] : (v2_relat_1(X0) | r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : (((v2_relat_1(X0) | (v1_xboole_0(k1_funct_1(X0,sK2(X0))) & r2_hidden(sK2(X0),k1_relat_1(X0)))) & (! [X2] : (~v1_xboole_0(k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0] : (? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0))) => (v1_xboole_0(k1_funct_1(X0,sK2(X0))) & r2_hidden(sK2(X0),k1_relat_1(X0))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0] : (((v2_relat_1(X0) | ? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X2] : (~v1_xboole_0(k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(rectify,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0] : (((v2_relat_1(X0) | ? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_relat_1(X0) <=> ! [X1] : ~(v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).
% 0.22/0.45  fof(f80,plain,(
% 0.22/0.45    spl5_8),
% 0.22/0.45    inference(avatar_split_clause,[],[f36,f78])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ( ! [X0] : (v2_relat_1(X0) | v1_xboole_0(k1_funct_1(X0,sK2(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    spl5_7),
% 0.22/0.45    inference(avatar_split_clause,[],[f27,f73])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    v1_relat_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    (~v2_relat_1(sK1) & k1_relat_1(sK0) = k1_relat_1(sK1) & v5_funct_1(sK0,sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(sK0) & v5_funct_1(sK0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ? [X1] : (~v2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(sK0) & v5_funct_1(sK0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v2_relat_1(sK1) & k1_relat_1(sK0) = k1_relat_1(sK1) & v5_funct_1(sK0,sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f6])).
% 0.22/0.45  fof(f6,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : ((~v2_relat_1(X1) & (k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.22/0.45    inference(negated_conjecture,[],[f4])).
% 0.22/0.45  fof(f4,conjecture,(
% 0.22/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    spl5_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f68])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    v1_funct_1(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    spl5_5),
% 0.22/0.45    inference(avatar_split_clause,[],[f29,f63])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    v1_relat_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    spl5_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f30,f58])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    v1_funct_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    spl5_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f31,f53])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    v5_funct_1(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    spl5_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f32,f48])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    ~spl5_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f33,f43])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ~v2_relat_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f14])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (23830)------------------------------
% 0.22/0.45  % (23830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (23830)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (23830)Memory used [KB]: 10618
% 0.22/0.45  % (23830)Time elapsed: 0.007 s
% 0.22/0.45  % (23830)------------------------------
% 0.22/0.45  % (23830)------------------------------
% 0.22/0.45  % (23824)Success in time 0.088 s
%------------------------------------------------------------------------------
