%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1186+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:26 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 436 expanded)
%              Number of leaves         :   47 ( 178 expanded)
%              Depth                    :   14
%              Number of atoms          :  918 (2458 expanded)
%              Number of equality atoms :   70 ( 143 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f101,f106,f110,f114,f118,f122,f126,f130,f139,f142,f165,f167,f178,f182,f186,f190,f193,f207,f219,f221,f240,f265,f273,f283,f285,f291,f297])).

fof(f297,plain,
    ( ~ spl4_6
    | ~ spl4_5
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f296,f289,f108,f112])).

fof(f112,plain,
    ( spl4_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f108,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f289,plain,
    ( spl4_30
  <=> r2_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f296,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_30 ),
    inference(resolution,[],[f290,f90])).

fof(f90,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f89])).

% (14445)Termination reason: Refutation not found, incomplete strategy

fof(f89,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f78])).

% (14445)Memory used [KB]: 1663
% (14445)Time elapsed: 0.026 s
% (14445)------------------------------
% (14445)------------------------------
fof(f78,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f290,plain,
    ( r2_orders_2(sK0,sK1,sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f289])).

fof(f291,plain,
    ( spl4_30
    | ~ spl4_2
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f287,f281,f95,f289])).

fof(f95,plain,
    ( spl4_2
  <=> r2_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f281,plain,
    ( spl4_29
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f287,plain,
    ( r2_orders_2(sK0,sK1,sK1)
    | ~ spl4_2
    | ~ spl4_29 ),
    inference(superposition,[],[f96,f282])).

fof(f282,plain,
    ( sK1 = sK2
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f281])).

fof(f96,plain,
    ( r2_orders_2(sK0,sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f285,plain,
    ( ~ spl4_3
    | ~ spl4_12
    | spl4_28 ),
    inference(avatar_split_clause,[],[f284,f278,f137,f99])).

fof(f99,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f137,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f278,plain,
    ( spl4_28
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f284,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_12
    | spl4_28 ),
    inference(resolution,[],[f279,f138])).

fof(f138,plain,
    ( ! [X0] :
        ( r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f279,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f278])).

fof(f283,plain,
    ( ~ spl4_28
    | spl4_29
    | ~ spl4_3
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f275,f271,f95,f99,f281,f278])).

fof(f271,plain,
    ( spl4_27
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X1,sK1)
        | sK1 = X1
        | ~ r2_hidden(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f275,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = sK2
    | ~ r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(resolution,[],[f272,f96])).

fof(f272,plain,
    ( ! [X1] :
        ( ~ r2_orders_2(sK0,X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK1 = X1
        | ~ r2_hidden(X1,u1_struct_0(sK0)) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f271])).

fof(f273,plain,
    ( ~ spl4_6
    | ~ spl4_5
    | spl4_27
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f268,f263,f271,f108,f112])).

fof(f263,plain,
    ( spl4_26
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK1)
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f268,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,u1_struct_0(sK0))
        | sK1 = X1
        | ~ r2_orders_2(sK0,X1,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_26 ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,u1_struct_0(sK0))
        | sK1 = X1
        | ~ r2_orders_2(sK0,X1,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_26 ),
    inference(resolution,[],[f264,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f264,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | sK1 = X0 )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( ~ spl4_6
    | ~ spl4_5
    | spl4_26
    | ~ spl4_1
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f260,f176,f92,f263,f108,f112])).

fof(f92,plain,
    ( spl4_1
  <=> r7_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f176,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ r7_orders_1(u1_orders_2(sK0),X1)
        | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | sK1 = X0
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_1
    | ~ spl4_16 ),
    inference(resolution,[],[f254,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f254,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | sK1 = X0 )
    | ~ spl4_1
    | ~ spl4_16 ),
    inference(resolution,[],[f102,f177])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ r7_orders_1(u1_orders_2(sK0),X1)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | X0 = X1 )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f102,plain,
    ( r7_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f240,plain,
    ( ~ spl4_21
    | spl4_1
    | ~ spl4_19
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f235,f217,f188,f92,f214])).

fof(f214,plain,
    ( spl4_21
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f188,plain,
    ( spl4_19
  <=> ! [X4] :
        ( ~ r2_hidden(X4,u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X4)
        | sK3(u1_orders_2(sK0),X4) != X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f217,plain,
    ( spl4_22
  <=> sK1 = sK3(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f235,plain,
    ( r7_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl4_19
    | ~ spl4_22 ),
    inference(trivial_inequality_removal,[],[f226])).

fof(f226,plain,
    ( sK1 != sK1
    | r7_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl4_19
    | ~ spl4_22 ),
    inference(superposition,[],[f189,f218])).

fof(f218,plain,
    ( sK1 = sK3(u1_orders_2(sK0),sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f217])).

fof(f189,plain,
    ( ! [X4] :
        ( sK3(u1_orders_2(sK0),X4) != X4
        | r7_orders_1(u1_orders_2(sK0),X4)
        | ~ r2_hidden(X4,u1_struct_0(sK0)) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f188])).

fof(f221,plain,
    ( ~ spl4_5
    | ~ spl4_12
    | spl4_21 ),
    inference(avatar_split_clause,[],[f220,f214,f137,f108])).

fof(f220,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_12
    | spl4_21 ),
    inference(resolution,[],[f215,f138])).

fof(f215,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f214])).

fof(f219,plain,
    ( ~ spl4_21
    | spl4_1
    | spl4_22
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f212,f205,f184,f180,f217,f92,f214])).

fof(f180,plain,
    ( spl4_17
  <=> ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X2)
        | r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),X2),X2),u1_orders_2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f184,plain,
    ( spl4_18
  <=> ! [X3] :
        ( ~ r2_hidden(X3,u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X3)
        | r2_hidden(sK3(u1_orders_2(sK0),X3),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f205,plain,
    ( spl4_20
  <=> ! [X0] :
        ( sK1 = sK3(u1_orders_2(sK0),X0)
        | ~ m1_subset_1(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),X0),sK1),u1_orders_2(sK0))
        | r7_orders_1(u1_orders_2(sK0),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f212,plain,
    ( sK1 = sK3(u1_orders_2(sK0),sK1)
    | r7_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,
    ( sK1 = sK3(u1_orders_2(sK0),sK1)
    | r7_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r7_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(resolution,[],[f209,f181])).

fof(f181,plain,
    ( ! [X2] :
        ( r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),X2),X2),u1_orders_2(sK0))
        | r7_orders_1(u1_orders_2(sK0),X2)
        | ~ r2_hidden(X2,u1_struct_0(sK0)) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),X0),sK1),u1_orders_2(sK0))
        | sK1 = sK3(u1_orders_2(sK0),X0)
        | r7_orders_1(u1_orders_2(sK0),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,
    ( ! [X0] :
        ( sK1 = sK3(u1_orders_2(sK0),X0)
        | ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),X0),sK1),u1_orders_2(sK0))
        | r7_orders_1(u1_orders_2(sK0),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(resolution,[],[f206,f194])).

fof(f194,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl4_18 ),
    inference(resolution,[],[f185,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f185,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(u1_orders_2(sK0),X3),u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X3)
        | ~ r2_hidden(X3,u1_struct_0(sK0)) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
        | sK1 = sK3(u1_orders_2(sK0),X0)
        | ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),X0),sK1),u1_orders_2(sK0))
        | r7_orders_1(u1_orders_2(sK0),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( ~ spl4_6
    | ~ spl4_5
    | spl4_20
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f201,f184,f112,f108,f104,f205,f108,f112])).

fof(f104,plain,
    ( spl4_4
  <=> ! [X3] :
        ( ~ r2_orders_2(sK0,X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f201,plain,
    ( ! [X0] :
        ( sK1 = sK3(u1_orders_2(sK0),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X0)
        | ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),X0),sK1),u1_orders_2(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(resolution,[],[f200,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK3(u1_orders_2(sK0),X0),sK1)
        | sK1 = sK3(u1_orders_2(sK0),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( ! [X0] :
        ( sK1 = sK3(u1_orders_2(sK0),X0)
        | ~ r1_orders_2(sK0,sK3(u1_orders_2(sK0),X0),sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X0)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(resolution,[],[f198,f194])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(u1_orders_2(sK0),X0),u1_struct_0(sK0))
        | sK1 = sK3(u1_orders_2(sK0),X0)
        | ~ r1_orders_2(sK0,sK3(u1_orders_2(sK0),X0),sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(resolution,[],[f195,f105])).

fof(f105,plain,
    ( ! [X3] :
        ( ~ r2_orders_2(sK0,X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f195,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK3(u1_orders_2(sK0),X0),sK1)
        | r7_orders_1(u1_orders_2(sK0),X0)
        | sK1 = sK3(u1_orders_2(sK0),X0)
        | ~ r1_orders_2(sK0,sK3(u1_orders_2(sK0),X0),sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(resolution,[],[f194,f147])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK1 = X0
        | ~ r1_orders_2(sK0,X0,sK1)
        | r2_orders_2(sK0,X0,sK1) )
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f146,f109])).

fof(f109,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | X0 = X1
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,X1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f79,f113])).

fof(f113,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f193,plain,
    ( ~ spl4_6
    | spl4_15 ),
    inference(avatar_split_clause,[],[f192,f173,f112])).

fof(f173,plain,
    ( spl4_15
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f192,plain,
    ( ~ l1_orders_2(sK0)
    | spl4_15 ),
    inference(resolution,[],[f191,f73])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f191,plain,
    ( ! [X0,X1] : ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_15 ),
    inference(resolution,[],[f174,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f174,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f190,plain,
    ( ~ spl4_15
    | spl4_19
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f171,f163,f188,f173])).

fof(f163,plain,
    ( spl4_14
  <=> u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f171,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,u1_struct_0(sK0))
        | sK3(u1_orders_2(sK0),X4) != X4
        | r7_orders_1(u1_orders_2(sK0),X4)
        | ~ v1_relat_1(u1_orders_2(sK0)) )
    | ~ spl4_14 ),
    inference(superposition,[],[f70,f164])).

fof(f164,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | sK3(X0,X1) != X1
      | r7_orders_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_orders_1(X0,X1)
            | ( r2_hidden(k4_tarski(sK3(X0,X1),X1),X0)
              & sK3(X0,X1) != X1
              & r2_hidden(sK3(X0,X1),k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r7_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(k4_tarski(X2,X1),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1),X1),X0)
        & sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_orders_1(X0,X1)
            | ? [X2] :
                ( r2_hidden(k4_tarski(X2,X1),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r7_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_orders_1(X0,X1)
            | ? [X2] :
                ( r2_hidden(k4_tarski(X2,X1),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r7_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_orders_1(X0,X1)
            | ? [X2] :
                ( r2_hidden(k4_tarski(X2,X1),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r7_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_orders_1(X0,X1)
        <=> ( ! [X2] :
                ~ ( r2_hidden(k4_tarski(X2,X1),X0)
                  & X1 != X2
                  & r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_1)).

fof(f186,plain,
    ( ~ spl4_15
    | spl4_18
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f170,f163,f184,f173])).

fof(f170,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,u1_struct_0(sK0))
        | r2_hidden(sK3(u1_orders_2(sK0),X3),u1_struct_0(sK0))
        | r7_orders_1(u1_orders_2(sK0),X3)
        | ~ v1_relat_1(u1_orders_2(sK0)) )
    | ~ spl4_14 ),
    inference(superposition,[],[f69,f164])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | r2_hidden(sK3(X0,X1),k3_relat_1(X0))
      | r7_orders_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f182,plain,
    ( ~ spl4_15
    | spl4_17
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f169,f163,f180,f173])).

fof(f169,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),X2),X2),u1_orders_2(sK0))
        | r7_orders_1(u1_orders_2(sK0),X2)
        | ~ v1_relat_1(u1_orders_2(sK0)) )
    | ~ spl4_14 ),
    inference(superposition,[],[f71,f164])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK3(X0,X1),X1),X0)
      | r7_orders_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f178,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f168,f163,f176,f173])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ r7_orders_1(u1_orders_2(sK0),X1)
        | ~ v1_relat_1(u1_orders_2(sK0)) )
    | ~ spl4_14 ),
    inference(superposition,[],[f68,f164])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_relat_1(X0))
      | X1 = X3
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r7_orders_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f167,plain,
    ( ~ spl4_6
    | ~ spl4_9
    | spl4_13 ),
    inference(avatar_split_clause,[],[f166,f160,f124,f112])).

fof(f124,plain,
    ( spl4_9
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f160,plain,
    ( spl4_13
  <=> v2_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f166,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | spl4_13 ),
    inference(resolution,[],[f161,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
       => v2_orders_2(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_orders_2)).

fof(f161,plain,
    ( ~ v2_orders_2(sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f165,plain,
    ( ~ spl4_9
    | ~ spl4_7
    | ~ spl4_13
    | spl4_14
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f156,f120,f112,f163,f160,f116,f124])).

fof(f116,plain,
    ( spl4_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f120,plain,
    ( spl4_8
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f156,plain,
    ( ~ l1_orders_2(sK0)
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ v2_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f155,f121])).

fof(f121,plain,
    ( v4_orders_2(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | u1_struct_0(X0) = k3_relat_1(u1_orders_2(X0))
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(global_subsumption,[],[f84,f154])).

fof(f154,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k3_relat_1(u1_orders_2(X0))
      | ~ v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k3_relat_1(u1_orders_2(X0))
      | ~ v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f152,f73])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(resolution,[],[f150,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v1_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_orders_2)).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_2(u1_orders_2(X0))
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(u1_orders_2(X0),X1)
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(resolution,[],[f144,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v2_orders_2(X0) )
     => v4_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_orders_2)).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_2(u1_orders_2(X0))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(resolution,[],[f87,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v2_orders_2(X0) )
     => v8_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_orders_2)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | k3_relat_1(X1) = X0
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v4_relat_2(X1)
        & v1_relat_2(X1) )
     => k3_relat_1(X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_orders_1)).

fof(f84,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_orders_2(X0) )
     => v1_partfun1(u1_orders_2(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_orders_2)).

fof(f142,plain,
    ( ~ spl4_6
    | spl4_11 ),
    inference(avatar_split_clause,[],[f140,f134,f112])).

fof(f134,plain,
    ( spl4_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f140,plain,
    ( ~ l1_orders_2(sK0)
    | spl4_11 ),
    inference(resolution,[],[f135,f72])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f135,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f139,plain,
    ( ~ spl4_11
    | spl4_12
    | spl4_10 ),
    inference(avatar_split_clause,[],[f132,f128,f137,f134])).

fof(f128,plain,
    ( spl4_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(sK0)
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | spl4_10 ),
    inference(resolution,[],[f131,f129])).

fof(f129,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f131,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | r2_hidden(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f86,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f130,plain,(
    ~ spl4_10 ),
    inference(avatar_split_clause,[],[f58,f128])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ( r2_orders_2(sK0,sK2,sK1)
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ r7_orders_1(u1_orders_2(sK0),sK1) )
    & ( ! [X3] :
          ( ~ r2_orders_2(sK0,X3,sK1)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | r7_orders_1(u1_orders_2(sK0),sK1) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( r2_orders_2(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r7_orders_1(u1_orders_2(X0),X1) )
            & ( ! [X3] :
                  ( ~ r2_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | r7_orders_1(u1_orders_2(X0),X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(sK0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ r7_orders_1(u1_orders_2(sK0),X1) )
          & ( ! [X3] :
                ( ~ r2_orders_2(sK0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            | r7_orders_1(u1_orders_2(sK0),X1) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( r2_orders_2(sK0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ r7_orders_1(u1_orders_2(sK0),X1) )
        & ( ! [X3] :
              ( ~ r2_orders_2(sK0,X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          | r7_orders_1(u1_orders_2(sK0),X1) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ? [X2] :
            ( r2_orders_2(sK0,X2,sK1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ r7_orders_1(u1_orders_2(sK0),sK1) )
      & ( ! [X3] :
            ( ~ r2_orders_2(sK0,X3,sK1)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        | r7_orders_1(u1_orders_2(sK0),sK1) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( r2_orders_2(sK0,X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( r2_orders_2(sK0,sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r7_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( ~ r2_orders_2(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r7_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r7_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r7_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r7_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r7_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r7_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r7_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( ~ r2_orders_2(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r7_orders_1(u1_orders_2(X0),X1)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r7_orders_1(u1_orders_2(X0),X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ r2_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_orders_2)).

fof(f126,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f59,f124])).

fof(f59,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f122,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f60,f120])).

fof(f60,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f118,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f61,f116])).

fof(f61,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f114,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f62,f112])).

fof(f62,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f110,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f63,f108])).

fof(f63,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,
    ( spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f64,f104,f92])).

fof(f64,plain,(
    ! [X3] :
      ( ~ r2_orders_2(sK0,X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r7_orders_1(u1_orders_2(sK0),sK1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f65,f99,f92])).

fof(f65,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r7_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f66,f95,f92])).

fof(f66,plain,
    ( r2_orders_2(sK0,sK2,sK1)
    | ~ r7_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f49])).

%------------------------------------------------------------------------------
