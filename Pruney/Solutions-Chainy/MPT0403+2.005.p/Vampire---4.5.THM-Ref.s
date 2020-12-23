%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 143 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :    6
%              Number of atoms          :  281 ( 456 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f342,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f45,f49,f61,f65,f69,f91,f103,f136,f148,f169,f185,f193,f198,f214,f257,f290,f312,f341])).

fof(f341,plain,
    ( ~ spl9_38
    | ~ spl9_2
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f335,f285,f43,f288])).

fof(f288,plain,
    ( spl9_38
  <=> r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f43,plain,
    ( spl9_2
  <=> ! [X0] : r1_setfam_1(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f285,plain,
    ( spl9_37
  <=> ! [X0] :
        ( ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0)
        | ~ r1_setfam_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f335,plain,
    ( ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0)
    | ~ spl9_2
    | ~ spl9_37 ),
    inference(resolution,[],[f286,f44])).

fof(f44,plain,
    ( ! [X0] : r1_setfam_1(X0,X0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ r1_setfam_1(X0,sK0)
        | ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0) )
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f285])).

fof(f312,plain,
    ( spl9_1
    | ~ spl9_3
    | spl9_38 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl9_1
    | ~ spl9_3
    | spl9_38 ),
    inference(subsumption_resolution,[],[f306,f40])).

fof(f40,plain,
    ( ~ r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl9_1
  <=> r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f306,plain,
    ( r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))
    | ~ spl9_3
    | spl9_38 ),
    inference(resolution,[],[f289,f48])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X0,X1),X0)
        | r1_setfam_1(X0,X1) )
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl9_3
  <=> ! [X1,X0] :
        ( r2_hidden(sK1(X0,X1),X0)
        | r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f289,plain,
    ( ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0)
    | spl9_38 ),
    inference(avatar_component_clause,[],[f288])).

fof(f290,plain,
    ( spl9_37
    | ~ spl9_38
    | ~ spl9_7
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f262,f255,f63,f288,f285])).

fof(f63,plain,
    ( spl9_7
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | r2_hidden(sK2(X1,X2),X1)
        | ~ r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f255,plain,
    ( spl9_34
  <=> ! [X4] :
        ( ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X4)
        | ~ r2_hidden(sK2(X4,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f262,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0)
        | ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0)
        | ~ r1_setfam_1(X0,sK0) )
    | ~ spl9_7
    | ~ spl9_34 ),
    inference(resolution,[],[f256,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X1,X2),X1)
        | ~ r2_hidden(X2,X0)
        | ~ r1_setfam_1(X0,X1) )
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f256,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK2(X4,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0)
        | ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X4) )
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( spl9_34
    | ~ spl9_27
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f235,f212,f183,f255])).

fof(f183,plain,
    ( spl9_27
  <=> ! [X5,X4,X6] :
        ( r2_hidden(X4,k2_setfam_1(X5,X6))
        | ~ r2_hidden(X4,X6)
        | ~ r2_hidden(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f212,plain,
    ( spl9_32
  <=> ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))
        | ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f235,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X4)
        | ~ r2_hidden(sK2(X4,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0) )
    | ~ spl9_27
    | ~ spl9_32 ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X4)
        | ~ r2_hidden(sK2(X4,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0)
        | ~ r2_hidden(sK2(X4,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0) )
    | ~ spl9_27
    | ~ spl9_32 ),
    inference(resolution,[],[f213,f184])).

fof(f184,plain,
    ( ! [X6,X4,X5] :
        ( r2_hidden(X4,k2_setfam_1(X5,X6))
        | ~ r2_hidden(X4,X6)
        | ~ r2_hidden(X4,X5) )
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f183])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))
        | ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0) )
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f212])).

fof(f214,plain,
    ( spl9_32
    | ~ spl9_2
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f203,f196,f43,f212])).

fof(f196,plain,
    ( spl9_29
  <=> ! [X1,X0] :
        ( ~ r1_setfam_1(X0,X1)
        | ~ r2_hidden(sK2(X1,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))
        | ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))
        | ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0) )
    | ~ spl9_2
    | ~ spl9_29 ),
    inference(resolution,[],[f197,f44])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        | ~ r2_hidden(sK2(X1,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))
        | ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0) )
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f196])).

fof(f198,plain,
    ( spl9_29
    | spl9_1
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f194,f191,f39,f196])).

fof(f191,plain,
    ( spl9_28
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(sK1(X0,X1),X2)
        | ~ r1_setfam_1(X2,X3)
        | ~ r2_hidden(sK2(X3,sK1(X0,X1)),X1)
        | r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        | ~ r2_hidden(sK2(X1,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0))
        | ~ r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0) )
    | spl9_1
    | ~ spl9_28 ),
    inference(resolution,[],[f192,f40])).

fof(f192,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_setfam_1(X0,X1)
        | ~ r1_setfam_1(X2,X3)
        | ~ r2_hidden(sK2(X3,sK1(X0,X1)),X1)
        | ~ r2_hidden(sK1(X0,X1),X2) )
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( spl9_28
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f82,f67,f59,f191])).

fof(f59,plain,
    ( spl9_6
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r1_tarski(sK1(X0,X1),X3)
        | r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f67,plain,
    ( spl9_8
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | r1_tarski(X2,sK2(X1,X2))
        | ~ r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f82,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(sK1(X0,X1),X2)
        | ~ r1_setfam_1(X2,X3)
        | ~ r2_hidden(sK2(X3,sK1(X0,X1)),X1)
        | r1_setfam_1(X0,X1) )
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(resolution,[],[f68,f60])).

fof(f60,plain,
    ( ! [X0,X3,X1] :
        ( ~ r1_tarski(sK1(X0,X1),X3)
        | ~ r2_hidden(X3,X1)
        | r1_setfam_1(X0,X1) )
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X2,sK2(X1,X2))
        | ~ r2_hidden(X2,X0)
        | ~ r1_setfam_1(X0,X1) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f185,plain,
    ( spl9_27
    | ~ spl9_13
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f171,f167,f89,f183])).

fof(f89,plain,
    ( spl9_13
  <=> ! [X1,X5,X0,X4] :
        ( ~ r2_hidden(X4,X0)
        | ~ r2_hidden(X5,X1)
        | r2_hidden(k2_xboole_0(X4,X5),k2_setfam_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f167,plain,
    ( spl9_25
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f171,plain,
    ( ! [X6,X4,X5] :
        ( r2_hidden(X4,k2_setfam_1(X5,X6))
        | ~ r2_hidden(X4,X6)
        | ~ r2_hidden(X4,X5) )
    | ~ spl9_13
    | ~ spl9_25 ),
    inference(superposition,[],[f90,f168])).

fof(f168,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f167])).

fof(f90,plain,
    ( ! [X4,X0,X5,X1] :
        ( r2_hidden(k2_xboole_0(X4,X5),k2_setfam_1(X0,X1))
        | ~ r2_hidden(X5,X1)
        | ~ r2_hidden(X4,X0) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f169,plain,
    ( spl9_25
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f157,f146,f101,f167])).

fof(f101,plain,
    ( spl9_16
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK3(X0,X1,X2),X1)
        | ~ r2_hidden(sK3(X0,X1,X2),X2)
        | k2_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f146,plain,
    ( spl9_22
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f157,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f156,f147])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f146])).

fof(f156,plain,
    ( ! [X0] :
        ( k2_xboole_0(X0,X0) = X0
        | ~ r2_hidden(sK3(X0,X0,X0),X0) )
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( ! [X0] :
        ( k2_xboole_0(X0,X0) = X0
        | ~ r2_hidden(sK3(X0,X0,X0),X0)
        | k2_xboole_0(X0,X0) = X0 )
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(resolution,[],[f147,f102])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        | ~ r2_hidden(sK3(X0,X1,X2),X1)
        | k2_xboole_0(X0,X1) = X2 )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f148,plain,
    ( spl9_22
    | ~ spl9_16
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f143,f134,f101,f146])).

fof(f134,plain,
    ( spl9_21
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK3(X0,X1,X2),X0)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X2)
        | k2_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl9_16
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f139,f102])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1,X1),X1)
        | r2_hidden(sK3(X0,X1,X1),X0)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl9_21 ),
    inference(factoring,[],[f135])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK3(X0,X1,X2),X2)
        | r2_hidden(sK3(X0,X1,X2),X1)
        | r2_hidden(sK3(X0,X1,X2),X0)
        | k2_xboole_0(X0,X1) = X2 )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,(
    spl9_21 ),
    inference(avatar_split_clause,[],[f18,f134])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f103,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f17,f101])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f91,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f34,f89])).

fof(f34,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k2_xboole_0(X4,X5),k2_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k2_xboole_0(X4,X5),X2)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k2_xboole_0(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k2_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_setfam_1)).

fof(f69,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f14,f67])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r1_tarski(X2,sK2(X1,X2))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f65,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f13,f63])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(sK2(X1,X2),X1)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f12,f59])).

fof(f12,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r1_tarski(sK1(X0,X1),X3)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f15,f47])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f11,f43])).

fof(f11,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] : r1_setfam_1(X0,X0) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_setfam_1(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_setfam_1)).

fof(f41,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f10,f39])).

fof(f10,plain,(
    ~ r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:50:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.43  % (12170)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (12169)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (12163)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (12172)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (12164)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (12177)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (12168)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (12162)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.52  % (12160)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.52  % (12176)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.53  % (12167)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.53  % (12171)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.53  % (12158)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (12174)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.53  % (12161)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (12159)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (12159)Refutation not found, incomplete strategy% (12159)------------------------------
% 0.20/0.54  % (12159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12159)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12159)Memory used [KB]: 10490
% 0.20/0.54  % (12159)Time elapsed: 0.106 s
% 0.20/0.54  % (12159)------------------------------
% 0.20/0.54  % (12159)------------------------------
% 0.20/0.55  % (12175)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.55  % (12158)Refutation not found, incomplete strategy% (12158)------------------------------
% 0.20/0.55  % (12158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12158)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12158)Memory used [KB]: 6140
% 0.20/0.55  % (12158)Time elapsed: 0.120 s
% 0.20/0.55  % (12158)------------------------------
% 0.20/0.55  % (12158)------------------------------
% 0.20/0.56  % (12173)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.56  % (12165)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.56  % (12167)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f342,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f41,f45,f49,f61,f65,f69,f91,f103,f136,f148,f169,f185,f193,f198,f214,f257,f290,f312,f341])).
% 0.20/0.56  fof(f341,plain,(
% 0.20/0.56    ~spl9_38 | ~spl9_2 | ~spl9_37),
% 0.20/0.56    inference(avatar_split_clause,[],[f335,f285,f43,f288])).
% 0.20/0.56  fof(f288,plain,(
% 0.20/0.56    spl9_38 <=> r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    spl9_2 <=> ! [X0] : r1_setfam_1(X0,X0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.56  fof(f285,plain,(
% 0.20/0.56    spl9_37 <=> ! [X0] : (~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0) | ~r1_setfam_1(X0,sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 0.20/0.56  fof(f335,plain,(
% 0.20/0.56    ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0) | (~spl9_2 | ~spl9_37)),
% 0.20/0.56    inference(resolution,[],[f286,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X0] : (r1_setfam_1(X0,X0)) ) | ~spl9_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f43])).
% 0.20/0.56  fof(f286,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_setfam_1(X0,sK0) | ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0)) ) | ~spl9_37),
% 0.20/0.56    inference(avatar_component_clause,[],[f285])).
% 0.20/0.56  fof(f312,plain,(
% 0.20/0.56    spl9_1 | ~spl9_3 | spl9_38),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f311])).
% 0.20/0.56  fof(f311,plain,(
% 0.20/0.56    $false | (spl9_1 | ~spl9_3 | spl9_38)),
% 0.20/0.56    inference(subsumption_resolution,[],[f306,f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ~r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) | spl9_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    spl9_1 <=> r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.56  fof(f306,plain,(
% 0.20/0.56    r1_setfam_1(sK0,k2_setfam_1(sK0,sK0)) | (~spl9_3 | spl9_38)),
% 0.20/0.56    inference(resolution,[],[f289,f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_setfam_1(X0,X1)) ) | ~spl9_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    spl9_3 <=> ! [X1,X0] : (r2_hidden(sK1(X0,X1),X0) | r1_setfam_1(X0,X1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.56  fof(f289,plain,(
% 0.20/0.56    ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0) | spl9_38),
% 0.20/0.56    inference(avatar_component_clause,[],[f288])).
% 0.20/0.56  fof(f290,plain,(
% 0.20/0.56    spl9_37 | ~spl9_38 | ~spl9_7 | ~spl9_34),
% 0.20/0.56    inference(avatar_split_clause,[],[f262,f255,f63,f288,f285])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    spl9_7 <=> ! [X1,X0,X2] : (~r2_hidden(X2,X0) | r2_hidden(sK2(X1,X2),X1) | ~r1_setfam_1(X0,X1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.20/0.56  fof(f255,plain,(
% 0.20/0.56    spl9_34 <=> ! [X4] : (~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X4) | ~r2_hidden(sK2(X4,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 0.20/0.56  fof(f262,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),sK0) | ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0) | ~r1_setfam_1(X0,sK0)) ) | (~spl9_7 | ~spl9_34)),
% 0.20/0.56    inference(resolution,[],[f256,f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK2(X1,X2),X1) | ~r2_hidden(X2,X0) | ~r1_setfam_1(X0,X1)) ) | ~spl9_7),
% 0.20/0.56    inference(avatar_component_clause,[],[f63])).
% 0.20/0.56  fof(f256,plain,(
% 0.20/0.56    ( ! [X4] : (~r2_hidden(sK2(X4,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0) | ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X4)) ) | ~spl9_34),
% 0.20/0.56    inference(avatar_component_clause,[],[f255])).
% 0.20/0.56  fof(f257,plain,(
% 0.20/0.56    spl9_34 | ~spl9_27 | ~spl9_32),
% 0.20/0.56    inference(avatar_split_clause,[],[f235,f212,f183,f255])).
% 0.20/0.56  fof(f183,plain,(
% 0.20/0.56    spl9_27 <=> ! [X5,X4,X6] : (r2_hidden(X4,k2_setfam_1(X5,X6)) | ~r2_hidden(X4,X6) | ~r2_hidden(X4,X5))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.20/0.56  fof(f212,plain,(
% 0.20/0.56    spl9_32 <=> ! [X0] : (~r2_hidden(sK2(X0,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0)) | ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 0.20/0.56  fof(f235,plain,(
% 0.20/0.56    ( ! [X4] : (~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X4) | ~r2_hidden(sK2(X4,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0)) ) | (~spl9_27 | ~spl9_32)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f231])).
% 0.20/0.56  fof(f231,plain,(
% 0.20/0.56    ( ! [X4] : (~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X4) | ~r2_hidden(sK2(X4,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0) | ~r2_hidden(sK2(X4,sK1(sK0,k2_setfam_1(sK0,sK0))),sK0)) ) | (~spl9_27 | ~spl9_32)),
% 0.20/0.56    inference(resolution,[],[f213,f184])).
% 0.20/0.56  fof(f184,plain,(
% 0.20/0.56    ( ! [X6,X4,X5] : (r2_hidden(X4,k2_setfam_1(X5,X6)) | ~r2_hidden(X4,X6) | ~r2_hidden(X4,X5)) ) | ~spl9_27),
% 0.20/0.56    inference(avatar_component_clause,[],[f183])).
% 0.20/0.56  fof(f213,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(sK2(X0,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0)) | ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0)) ) | ~spl9_32),
% 0.20/0.56    inference(avatar_component_clause,[],[f212])).
% 0.20/0.56  fof(f214,plain,(
% 0.20/0.56    spl9_32 | ~spl9_2 | ~spl9_29),
% 0.20/0.56    inference(avatar_split_clause,[],[f203,f196,f43,f212])).
% 0.20/0.56  fof(f196,plain,(
% 0.20/0.56    spl9_29 <=> ! [X1,X0] : (~r1_setfam_1(X0,X1) | ~r2_hidden(sK2(X1,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0)) | ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.20/0.56  fof(f203,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(sK2(X0,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0)) | ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0)) ) | (~spl9_2 | ~spl9_29)),
% 0.20/0.56    inference(resolution,[],[f197,f44])).
% 0.20/0.56  fof(f197,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(sK2(X1,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0)) | ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0)) ) | ~spl9_29),
% 0.20/0.56    inference(avatar_component_clause,[],[f196])).
% 0.20/0.56  fof(f198,plain,(
% 0.20/0.56    spl9_29 | spl9_1 | ~spl9_28),
% 0.20/0.56    inference(avatar_split_clause,[],[f194,f191,f39,f196])).
% 0.20/0.56  fof(f191,plain,(
% 0.20/0.56    spl9_28 <=> ! [X1,X3,X0,X2] : (~r2_hidden(sK1(X0,X1),X2) | ~r1_setfam_1(X2,X3) | ~r2_hidden(sK2(X3,sK1(X0,X1)),X1) | r1_setfam_1(X0,X1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 0.20/0.56  fof(f194,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(sK2(X1,sK1(sK0,k2_setfam_1(sK0,sK0))),k2_setfam_1(sK0,sK0)) | ~r2_hidden(sK1(sK0,k2_setfam_1(sK0,sK0)),X0)) ) | (spl9_1 | ~spl9_28)),
% 0.20/0.56    inference(resolution,[],[f192,f40])).
% 0.20/0.56  fof(f192,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (r1_setfam_1(X0,X1) | ~r1_setfam_1(X2,X3) | ~r2_hidden(sK2(X3,sK1(X0,X1)),X1) | ~r2_hidden(sK1(X0,X1),X2)) ) | ~spl9_28),
% 0.20/0.56    inference(avatar_component_clause,[],[f191])).
% 0.20/0.56  fof(f193,plain,(
% 0.20/0.56    spl9_28 | ~spl9_6 | ~spl9_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f82,f67,f59,f191])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    spl9_6 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r1_tarski(sK1(X0,X1),X3) | r1_setfam_1(X0,X1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    spl9_8 <=> ! [X1,X0,X2] : (~r2_hidden(X2,X0) | r1_tarski(X2,sK2(X1,X2)) | ~r1_setfam_1(X0,X1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK1(X0,X1),X2) | ~r1_setfam_1(X2,X3) | ~r2_hidden(sK2(X3,sK1(X0,X1)),X1) | r1_setfam_1(X0,X1)) ) | (~spl9_6 | ~spl9_8)),
% 0.20/0.56    inference(resolution,[],[f68,f60])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r1_tarski(sK1(X0,X1),X3) | ~r2_hidden(X3,X1) | r1_setfam_1(X0,X1)) ) | ~spl9_6),
% 0.20/0.56    inference(avatar_component_clause,[],[f59])).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,sK2(X1,X2)) | ~r2_hidden(X2,X0) | ~r1_setfam_1(X0,X1)) ) | ~spl9_8),
% 0.20/0.56    inference(avatar_component_clause,[],[f67])).
% 0.20/0.56  fof(f185,plain,(
% 0.20/0.56    spl9_27 | ~spl9_13 | ~spl9_25),
% 0.20/0.56    inference(avatar_split_clause,[],[f171,f167,f89,f183])).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    spl9_13 <=> ! [X1,X5,X0,X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k2_xboole_0(X4,X5),k2_setfam_1(X0,X1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    spl9_25 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.20/0.56  fof(f171,plain,(
% 0.20/0.56    ( ! [X6,X4,X5] : (r2_hidden(X4,k2_setfam_1(X5,X6)) | ~r2_hidden(X4,X6) | ~r2_hidden(X4,X5)) ) | (~spl9_13 | ~spl9_25)),
% 0.20/0.56    inference(superposition,[],[f90,f168])).
% 0.20/0.56  fof(f168,plain,(
% 0.20/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl9_25),
% 0.20/0.56    inference(avatar_component_clause,[],[f167])).
% 0.20/0.56  fof(f90,plain,(
% 0.20/0.56    ( ! [X4,X0,X5,X1] : (r2_hidden(k2_xboole_0(X4,X5),k2_setfam_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) ) | ~spl9_13),
% 0.20/0.56    inference(avatar_component_clause,[],[f89])).
% 0.20/0.56  fof(f169,plain,(
% 0.20/0.56    spl9_25 | ~spl9_16 | ~spl9_22),
% 0.20/0.56    inference(avatar_split_clause,[],[f157,f146,f101,f167])).
% 0.20/0.56  fof(f101,plain,(
% 0.20/0.56    spl9_16 <=> ! [X1,X0,X2] : (~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.20/0.56  fof(f146,plain,(
% 0.20/0.56    spl9_22 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.20/0.56  fof(f157,plain,(
% 0.20/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | (~spl9_16 | ~spl9_22)),
% 0.20/0.56    inference(subsumption_resolution,[],[f156,f147])).
% 0.20/0.56  fof(f147,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | ~spl9_22),
% 0.20/0.56    inference(avatar_component_clause,[],[f146])).
% 0.20/0.56  fof(f156,plain,(
% 0.20/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0 | ~r2_hidden(sK3(X0,X0,X0),X0)) ) | (~spl9_16 | ~spl9_22)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f153])).
% 0.20/0.56  fof(f153,plain,(
% 0.20/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0 | ~r2_hidden(sK3(X0,X0,X0),X0) | k2_xboole_0(X0,X0) = X0) ) | (~spl9_16 | ~spl9_22)),
% 0.20/0.56    inference(resolution,[],[f147,f102])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | k2_xboole_0(X0,X1) = X2) ) | ~spl9_16),
% 0.20/0.56    inference(avatar_component_clause,[],[f101])).
% 0.20/0.56  fof(f148,plain,(
% 0.20/0.56    spl9_22 | ~spl9_16 | ~spl9_21),
% 0.20/0.56    inference(avatar_split_clause,[],[f143,f134,f101,f146])).
% 0.20/0.56  fof(f134,plain,(
% 0.20/0.56    spl9_21 <=> ! [X1,X0,X2] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.20/0.56  fof(f143,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | (~spl9_16 | ~spl9_21)),
% 0.20/0.56    inference(subsumption_resolution,[],[f139,f102])).
% 0.20/0.56  fof(f139,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | r2_hidden(sK3(X0,X1,X1),X0) | k2_xboole_0(X0,X1) = X1) ) | ~spl9_21),
% 0.20/0.56    inference(factoring,[],[f135])).
% 0.20/0.56  fof(f135,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | k2_xboole_0(X0,X1) = X2) ) | ~spl9_21),
% 0.20/0.56    inference(avatar_component_clause,[],[f134])).
% 0.20/0.56  fof(f136,plain,(
% 0.20/0.56    spl9_21),
% 0.20/0.56    inference(avatar_split_clause,[],[f18,f134])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    spl9_16),
% 0.20/0.56    inference(avatar_split_clause,[],[f17,f101])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    spl9_13),
% 0.20/0.56    inference(avatar_split_clause,[],[f34,f89])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ( ! [X4,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k2_xboole_0(X4,X5),k2_setfam_1(X0,X1))) )),
% 0.20/0.56    inference(equality_resolution,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k2_xboole_0(X4,X5),X2) | k2_setfam_1(X0,X1) != X2) )),
% 0.20/0.56    inference(equality_resolution,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k2_xboole_0(X4,X5) != X3 | r2_hidden(X3,X2) | k2_setfam_1(X0,X1) != X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (k2_setfam_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k2_xboole_0(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_setfam_1)).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    spl9_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f14,f67])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r1_tarski(X2,sK2(X1,X2)) | ~r1_setfam_1(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    spl9_7),
% 0.20/0.56    inference(avatar_split_clause,[],[f13,f63])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(sK2(X1,X2),X1) | ~r1_setfam_1(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    spl9_6),
% 0.20/0.56    inference(avatar_split_clause,[],[f12,f59])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r1_tarski(sK1(X0,X1),X3) | r1_setfam_1(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    spl9_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f15,f47])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    spl9_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f11,f43])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ( ! [X0] : (r1_setfam_1(X0,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,plain,(
% 0.20/0.56    ! [X0] : r1_setfam_1(X0,X0)),
% 0.20/0.56    inference(rectify,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : r1_setfam_1(X0,X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_setfam_1)).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ~spl9_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f10,f39])).
% 0.20/0.56  fof(f10,plain,(
% 0.20/0.56    ~r1_setfam_1(sK0,k2_setfam_1(sK0,sK0))),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,plain,(
% 0.20/0.56    ? [X0] : ~r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,negated_conjecture,(
% 0.20/0.56    ~! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.20/0.56    inference(negated_conjecture,[],[f5])).
% 0.20/0.56  fof(f5,conjecture,(
% 0.20/0.56    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_setfam_1)).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (12167)------------------------------
% 0.20/0.56  % (12167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (12167)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (12167)Memory used [KB]: 10874
% 0.20/0.56  % (12167)Time elapsed: 0.144 s
% 0.20/0.56  % (12167)------------------------------
% 0.20/0.56  % (12167)------------------------------
% 0.20/0.56  % (12157)Success in time 0.202 s
%------------------------------------------------------------------------------
