%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 308 expanded)
%              Number of leaves         :   33 ( 126 expanded)
%              Depth                    :   14
%              Number of atoms          :  701 (1307 expanded)
%              Number of equality atoms :   27 (  81 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f105,f110,f125,f146,f148,f150,f161,f178,f217,f224,f232,f234,f241])).

fof(f241,plain,
    ( ~ spl4_10
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_7
    | ~ spl4_6
    | spl4_23 ),
    inference(avatar_split_clause,[],[f240,f230,f103,f108,f141,f87,f138])).

fof(f138,plain,
    ( spl4_10
  <=> v5_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f87,plain,
    ( spl4_4
  <=> v2_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f141,plain,
    ( spl4_11
  <=> l1_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f108,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f103,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f230,plain,
    ( spl4_23
  <=> r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f240,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_23 ),
    inference(forward_demodulation,[],[f239,f51])).

fof(f51,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f239,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_23 ),
    inference(forward_demodulation,[],[f237,f51])).

fof(f237,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_23 ),
    inference(resolution,[],[f231,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f73,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

fof(f231,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f230])).

fof(f234,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | spl4_22 ),
    inference(avatar_split_clause,[],[f233,f227,f108,f103,f87])).

fof(f227,plain,
    ( spl4_22
  <=> m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f233,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ v2_lattice3(k2_yellow_1(sK0))
    | spl4_22 ),
    inference(resolution,[],[f228,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v2_lattice3(k2_yellow_1(X0)) ) ),
    inference(global_subsumption,[],[f49,f50,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f66,f51])).

fof(f50,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f49,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f228,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f227])).

fof(f232,plain,
    ( ~ spl4_22
    | ~ spl4_23
    | ~ spl4_6
    | ~ spl4_8
    | spl4_21 ),
    inference(avatar_split_clause,[],[f225,f222,f123,f103,f230,f227])).

fof(f123,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f222,plain,
    ( spl4_21
  <=> r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f225,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | ~ spl4_6
    | ~ spl4_8
    | spl4_21 ),
    inference(resolution,[],[f223,f126])).

fof(f126,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,sK1)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f124,f104])).

fof(f104,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | r1_tarski(X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f223,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f222])).

fof(f224,plain,
    ( ~ spl4_21
    | ~ spl4_6
    | spl4_13
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f218,f215,f159,f103,f222])).

fof(f159,plain,
    ( spl4_13
  <=> r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f215,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),X1)
        | ~ m1_subset_1(X0,sK0)
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),k1_setfam_1(k2_tarski(X1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f218,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl4_13
    | ~ spl4_20 ),
    inference(resolution,[],[f216,f160])).

fof(f160,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),k1_setfam_1(k2_tarski(X1,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),X1) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f215])).

fof(f217,plain,
    ( ~ spl4_4
    | ~ spl4_7
    | spl4_20
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f213,f176,f215,f108,f87])).

fof(f176,plain,
    ( spl4_15
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),X3)
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),k1_setfam_1(k2_tarski(X3,sK2)))
        | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X2,sK2),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),X1)
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),k1_setfam_1(k2_tarski(X1,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK2,sK0)
        | ~ v2_lattice3(k2_yellow_1(sK0)) )
    | ~ spl4_15 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),X1)
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),k1_setfam_1(k2_tarski(X1,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK2,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ v2_lattice3(k2_yellow_1(sK0)) )
    | ~ spl4_15 ),
    inference(resolution,[],[f177,f112])).

fof(f177,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X2,sK2),sK0)
        | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),X3)
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),k1_setfam_1(k2_tarski(X3,sK2)))
        | ~ m1_subset_1(X2,sK0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( ~ spl4_10
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_7
    | spl4_15
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f174,f123,f108,f176,f108,f141,f87,f138])).

fof(f174,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(sK2,sK0)
        | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X2,sK2),sK0)
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),k1_setfam_1(k2_tarski(X3,sK2)))
        | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),X3)
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v2_lattice3(k2_yellow_1(sK0))
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f173,f51])).

fof(f173,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2,sK0)
        | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X2,sK2),sK0)
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),k1_setfam_1(k2_tarski(X3,sK2)))
        | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),X3)
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v2_lattice3(k2_yellow_1(sK0))
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f165,f51])).

fof(f165,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X2,sK2),sK0)
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),k1_setfam_1(k2_tarski(X3,sK2)))
        | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),X3)
        | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v2_lattice3(k2_yellow_1(sK0))
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f154,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f72,f66])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f154,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X2,sK2)
        | ~ m1_subset_1(X2,sK0)
        | r1_tarski(X2,k1_setfam_1(k2_tarski(X3,sK2)))
        | ~ r1_tarski(X2,X3) )
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f127,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f63])).

fof(f63,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f127,plain,
    ( ! [X1] :
        ( r1_tarski(X1,sK2)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,sK2)
        | ~ m1_subset_1(X1,sK0) )
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f124,f109])).

fof(f109,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f161,plain,
    ( ~ spl4_7
    | ~ spl4_6
    | ~ spl4_13
    | spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f155,f144,f75,f159,f103,f108])).

fof(f75,plain,
    ( spl4_1
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f144,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,sK0)
        | k12_lattice3(k2_yellow_1(sK0),X1,X0) = k11_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f155,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | spl4_1
    | ~ spl4_12 ),
    inference(superposition,[],[f76,f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( k12_lattice3(k2_yellow_1(sK0),X1,X0) = k11_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f144])).

fof(f76,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f150,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl4_11 ),
    inference(resolution,[],[f142,f50])).

fof(f142,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f148,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f139,f49])).

fof(f139,plain,
    ( ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f146,plain,
    ( ~ spl4_10
    | ~ spl4_11
    | spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f136,f87,f144,f141,f138])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | k12_lattice3(k2_yellow_1(sK0),X1,X0) = k11_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f135,f51])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | k12_lattice3(k2_yellow_1(sK0),X1,X0) = k11_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f134,f51])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | k12_lattice3(k2_yellow_1(sK0),X1,X0) = k11_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f67,f88])).

fof(f88,plain,
    ( v2_lattice3(k2_yellow_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f125,plain,
    ( spl4_5
    | spl4_8
    | spl4_5 ),
    inference(avatar_split_clause,[],[f120,f91,f123,f91])).

fof(f91,plain,
    ( spl4_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | r1_tarski(X0,X1)
        | v1_xboole_0(sK0) )
    | spl4_5 ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X1,sK0)
        | r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK0) )
    | spl4_5 ),
    inference(resolution,[],[f118,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f96,f51])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f54,f51])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f118,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | spl4_5 ),
    inference(resolution,[],[f117,f92])).

fof(f92,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_orders_2(k2_yellow_1(X1),X2,X0)
      | r3_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f116,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f48,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f114,f51])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f113,f51])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f65,f50])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f48,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,
    ( spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f106,f79,f108])).

fof(f79,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f106,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f80,f51])).

fof(f80,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f105,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f101,f83,f103])).

fof(f83,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f101,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f84,f51])).

fof(f84,plain,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f93,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f43,f91])).

fof(f43,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v2_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f89,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f44,f87])).

fof(f44,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f45,f83])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f46,f79])).

fof(f46,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f69,f75])).

fof(f69,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) ),
    inference(definition_unfolding,[],[f47,f63])).

fof(f47,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (25868)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (25888)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (25880)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.50  % (25871)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.50  % (25885)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.50  % (25868)Refutation not found, incomplete strategy% (25868)------------------------------
% 0.19/0.50  % (25868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (25868)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (25868)Memory used [KB]: 10746
% 0.19/0.50  % (25868)Time elapsed: 0.085 s
% 0.19/0.50  % (25868)------------------------------
% 0.19/0.50  % (25868)------------------------------
% 0.19/0.50  % (25872)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (25888)Refutation not found, incomplete strategy% (25888)------------------------------
% 0.19/0.51  % (25888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (25888)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (25888)Memory used [KB]: 10746
% 0.19/0.51  % (25888)Time elapsed: 0.063 s
% 0.19/0.51  % (25888)------------------------------
% 0.19/0.51  % (25888)------------------------------
% 0.19/0.51  % (25885)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f248,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f105,f110,f125,f146,f148,f150,f161,f178,f217,f224,f232,f234,f241])).
% 0.19/0.51  fof(f241,plain,(
% 0.19/0.51    ~spl4_10 | ~spl4_4 | ~spl4_11 | ~spl4_7 | ~spl4_6 | spl4_23),
% 0.19/0.51    inference(avatar_split_clause,[],[f240,f230,f103,f108,f141,f87,f138])).
% 0.19/0.51  fof(f138,plain,(
% 0.19/0.51    spl4_10 <=> v5_orders_2(k2_yellow_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    spl4_4 <=> v2_lattice3(k2_yellow_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.51  fof(f141,plain,(
% 0.19/0.51    spl4_11 <=> l1_orders_2(k2_yellow_1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.19/0.51  fof(f108,plain,(
% 0.19/0.51    spl4_7 <=> m1_subset_1(sK2,sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.51  fof(f103,plain,(
% 0.19/0.51    spl4_6 <=> m1_subset_1(sK1,sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.51  fof(f230,plain,(
% 0.19/0.51    spl4_23 <=> r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.19/0.51  fof(f240,plain,(
% 0.19/0.51    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | spl4_23),
% 0.19/0.51    inference(forward_demodulation,[],[f239,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.19/0.51  fof(f239,plain,(
% 0.19/0.51    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | spl4_23),
% 0.19/0.51    inference(forward_demodulation,[],[f237,f51])).
% 0.19/0.51  fof(f237,plain,(
% 0.19/0.51    ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | spl4_23),
% 0.19/0.51    inference(resolution,[],[f231,f98])).
% 0.19/0.51  fof(f98,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f73,f66])).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.19/0.51    inference(flattening,[],[f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f56])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X1) | k12_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f41])).
% 0.19/0.51  fof(f41,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.19/0.51    inference(rectify,[],[f38])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.19/0.51    inference(flattening,[],[f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.19/0.51    inference(nnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.19/0.51    inference(flattening,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).
% 0.19/0.51  fof(f231,plain,(
% 0.19/0.51    ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl4_23),
% 0.19/0.51    inference(avatar_component_clause,[],[f230])).
% 0.19/0.51  fof(f234,plain,(
% 0.19/0.51    ~spl4_4 | ~spl4_6 | ~spl4_7 | spl4_22),
% 0.19/0.51    inference(avatar_split_clause,[],[f233,f227,f108,f103,f87])).
% 0.19/0.51  fof(f227,plain,(
% 0.19/0.51    spl4_22 <=> m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.19/0.51  fof(f233,plain,(
% 0.19/0.51    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | ~v2_lattice3(k2_yellow_1(sK0)) | spl4_22),
% 0.19/0.51    inference(resolution,[],[f228,f112])).
% 0.19/0.51  fof(f112,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~v2_lattice3(k2_yellow_1(X0))) )),
% 0.19/0.51    inference(global_subsumption,[],[f49,f50,f111])).
% 0.19/0.51  fof(f111,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.19/0.51    inference(superposition,[],[f66,f51])).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.19/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.19/0.51    inference(pure_predicate_removal,[],[f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.19/0.51    inference(pure_predicate_removal,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.19/0.51  fof(f228,plain,(
% 0.19/0.51    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | spl4_22),
% 0.19/0.51    inference(avatar_component_clause,[],[f227])).
% 0.19/0.51  fof(f232,plain,(
% 0.19/0.51    ~spl4_22 | ~spl4_23 | ~spl4_6 | ~spl4_8 | spl4_21),
% 0.19/0.51    inference(avatar_split_clause,[],[f225,f222,f123,f103,f230,f227])).
% 0.19/0.51  fof(f123,plain,(
% 0.19/0.51    spl4_8 <=> ! [X1,X0] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | r1_tarski(X0,X1) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.51  fof(f222,plain,(
% 0.19/0.51    spl4_21 <=> r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.19/0.51  fof(f225,plain,(
% 0.19/0.51    ~r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | (~spl4_6 | ~spl4_8 | spl4_21)),
% 0.19/0.51    inference(resolution,[],[f223,f126])).
% 0.19/0.51  fof(f126,plain,(
% 0.19/0.51    ( ! [X0] : (r1_tarski(X0,sK1) | ~r1_orders_2(k2_yellow_1(sK0),X0,sK1) | ~m1_subset_1(X0,sK0)) ) | (~spl4_6 | ~spl4_8)),
% 0.19/0.51    inference(resolution,[],[f124,f104])).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    m1_subset_1(sK1,sK0) | ~spl4_6),
% 0.19/0.51    inference(avatar_component_clause,[],[f103])).
% 0.19/0.51  fof(f124,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | r1_tarski(X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0)) ) | ~spl4_8),
% 0.19/0.51    inference(avatar_component_clause,[],[f123])).
% 0.19/0.51  fof(f223,plain,(
% 0.19/0.51    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl4_21),
% 0.19/0.51    inference(avatar_component_clause,[],[f222])).
% 0.19/0.51  fof(f224,plain,(
% 0.19/0.51    ~spl4_21 | ~spl4_6 | spl4_13 | ~spl4_20),
% 0.19/0.51    inference(avatar_split_clause,[],[f218,f215,f159,f103,f222])).
% 0.19/0.51  fof(f159,plain,(
% 0.19/0.51    spl4_13 <=> r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.19/0.51  fof(f215,plain,(
% 0.19/0.51    spl4_20 <=> ! [X1,X0] : (~r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),X1) | ~m1_subset_1(X0,sK0) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),k1_setfam_1(k2_tarski(X1,sK2))))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.19/0.51  fof(f218,plain,(
% 0.19/0.51    ~m1_subset_1(sK1,sK0) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (spl4_13 | ~spl4_20)),
% 0.19/0.51    inference(resolution,[],[f216,f160])).
% 0.19/0.51  fof(f160,plain,(
% 0.19/0.51    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) | spl4_13),
% 0.19/0.51    inference(avatar_component_clause,[],[f159])).
% 0.19/0.51  fof(f216,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),k1_setfam_1(k2_tarski(X1,sK2))) | ~m1_subset_1(X0,sK0) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),X1)) ) | ~spl4_20),
% 0.19/0.51    inference(avatar_component_clause,[],[f215])).
% 0.19/0.51  fof(f217,plain,(
% 0.19/0.51    ~spl4_4 | ~spl4_7 | spl4_20 | ~spl4_15),
% 0.19/0.51    inference(avatar_split_clause,[],[f213,f176,f215,f108,f87])).
% 0.19/0.51  fof(f176,plain,(
% 0.19/0.51    spl4_15 <=> ! [X3,X2] : (~m1_subset_1(X2,sK0) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),X3) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),k1_setfam_1(k2_tarski(X3,sK2))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X2,sK2),sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.19/0.51  fof(f213,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),X1) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),k1_setfam_1(k2_tarski(X1,sK2))) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK2,sK0) | ~v2_lattice3(k2_yellow_1(sK0))) ) | ~spl4_15),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f212])).
% 0.19/0.51  fof(f212,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),X1) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,sK2),k1_setfam_1(k2_tarski(X1,sK2))) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(X0,sK0) | ~v2_lattice3(k2_yellow_1(sK0))) ) | ~spl4_15),
% 0.19/0.51    inference(resolution,[],[f177,f112])).
% 0.19/0.51  fof(f177,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X2,sK2),sK0) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),X3) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),k1_setfam_1(k2_tarski(X3,sK2))) | ~m1_subset_1(X2,sK0)) ) | ~spl4_15),
% 0.19/0.51    inference(avatar_component_clause,[],[f176])).
% 0.19/0.51  fof(f178,plain,(
% 0.19/0.51    ~spl4_10 | ~spl4_4 | ~spl4_11 | ~spl4_7 | spl4_15 | ~spl4_7 | ~spl4_8),
% 0.19/0.51    inference(avatar_split_clause,[],[f174,f123,f108,f176,f108,f141,f87,f138])).
% 0.19/0.51  fof(f174,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,sK0) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X2,sK2),sK0) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),k1_setfam_1(k2_tarski(X3,sK2))) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),X3) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))) ) | (~spl4_7 | ~spl4_8)),
% 0.19/0.51    inference(forward_demodulation,[],[f173,f51])).
% 0.19/0.51  fof(f173,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~m1_subset_1(sK2,sK0) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X2,sK2),sK0) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),k1_setfam_1(k2_tarski(X3,sK2))) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),X3) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))) ) | (~spl4_7 | ~spl4_8)),
% 0.19/0.51    inference(forward_demodulation,[],[f165,f51])).
% 0.19/0.51  fof(f165,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X2,sK2),sK0) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),k1_setfam_1(k2_tarski(X3,sK2))) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),X2,sK2),X3) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))) ) | (~spl4_7 | ~spl4_8)),
% 0.19/0.51    inference(resolution,[],[f154,f99])).
% 0.19/0.51  fof(f99,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f72,f66])).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f57])).
% 0.19/0.51  fof(f57,plain,(
% 0.19/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k12_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f41])).
% 0.19/0.51  fof(f154,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~r1_orders_2(k2_yellow_1(sK0),X2,sK2) | ~m1_subset_1(X2,sK0) | r1_tarski(X2,k1_setfam_1(k2_tarski(X3,sK2))) | ~r1_tarski(X2,X3)) ) | (~spl4_7 | ~spl4_8)),
% 0.19/0.51    inference(resolution,[],[f127,f70])).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(definition_unfolding,[],[f68,f63])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.51    inference(flattening,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.19/0.51  fof(f127,plain,(
% 0.19/0.51    ( ! [X1] : (r1_tarski(X1,sK2) | ~r1_orders_2(k2_yellow_1(sK0),X1,sK2) | ~m1_subset_1(X1,sK0)) ) | (~spl4_7 | ~spl4_8)),
% 0.19/0.51    inference(resolution,[],[f124,f109])).
% 0.19/0.51  fof(f109,plain,(
% 0.19/0.51    m1_subset_1(sK2,sK0) | ~spl4_7),
% 0.19/0.51    inference(avatar_component_clause,[],[f108])).
% 0.19/0.51  fof(f161,plain,(
% 0.19/0.51    ~spl4_7 | ~spl4_6 | ~spl4_13 | spl4_1 | ~spl4_12),
% 0.19/0.51    inference(avatar_split_clause,[],[f155,f144,f75,f159,f103,f108])).
% 0.19/0.51  fof(f75,plain,(
% 0.19/0.51    spl4_1 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.51  fof(f144,plain,(
% 0.19/0.51    spl4_12 <=> ! [X1,X0] : (~m1_subset_1(X1,sK0) | k12_lattice3(k2_yellow_1(sK0),X1,X0) = k11_lattice3(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X0,sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.19/0.51  fof(f155,plain,(
% 0.19/0.51    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) | ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | (spl4_1 | ~spl4_12)),
% 0.19/0.51    inference(superposition,[],[f76,f145])).
% 0.19/0.51  fof(f145,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k12_lattice3(k2_yellow_1(sK0),X1,X0) = k11_lattice3(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl4_12),
% 0.19/0.51    inference(avatar_component_clause,[],[f144])).
% 0.19/0.51  fof(f76,plain,(
% 0.19/0.51    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2))) | spl4_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f75])).
% 0.19/0.51  fof(f150,plain,(
% 0.19/0.51    spl4_11),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f149])).
% 0.19/0.51  fof(f149,plain,(
% 0.19/0.51    $false | spl4_11),
% 0.19/0.51    inference(resolution,[],[f142,f50])).
% 0.19/0.51  fof(f142,plain,(
% 0.19/0.51    ~l1_orders_2(k2_yellow_1(sK0)) | spl4_11),
% 0.19/0.51    inference(avatar_component_clause,[],[f141])).
% 0.19/0.51  fof(f148,plain,(
% 0.19/0.51    spl4_10),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f147])).
% 0.19/0.51  fof(f147,plain,(
% 0.19/0.51    $false | spl4_10),
% 0.19/0.51    inference(resolution,[],[f139,f49])).
% 0.19/0.51  fof(f139,plain,(
% 0.19/0.51    ~v5_orders_2(k2_yellow_1(sK0)) | spl4_10),
% 0.19/0.51    inference(avatar_component_clause,[],[f138])).
% 0.19/0.51  fof(f146,plain,(
% 0.19/0.51    ~spl4_10 | ~spl4_11 | spl4_12 | ~spl4_4),
% 0.19/0.51    inference(avatar_split_clause,[],[f136,f87,f144,f141,f138])).
% 0.19/0.51  fof(f136,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~l1_orders_2(k2_yellow_1(sK0)) | k12_lattice3(k2_yellow_1(sK0),X1,X0) = k11_lattice3(k2_yellow_1(sK0),X1,X0) | ~v5_orders_2(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.19/0.51    inference(forward_demodulation,[],[f135,f51])).
% 0.19/0.51  fof(f135,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | k12_lattice3(k2_yellow_1(sK0),X1,X0) = k11_lattice3(k2_yellow_1(sK0),X1,X0) | ~v5_orders_2(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.19/0.51    inference(forward_demodulation,[],[f134,f51])).
% 0.19/0.51  fof(f134,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | k12_lattice3(k2_yellow_1(sK0),X1,X0) = k11_lattice3(k2_yellow_1(sK0),X1,X0) | ~v5_orders_2(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.19/0.51    inference(resolution,[],[f67,f88])).
% 0.19/0.51  fof(f88,plain,(
% 0.19/0.51    v2_lattice3(k2_yellow_1(sK0)) | ~spl4_4),
% 0.19/0.51    inference(avatar_component_clause,[],[f87])).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~v5_orders_2(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.19/0.51    inference(flattening,[],[f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.19/0.51  fof(f125,plain,(
% 0.19/0.51    spl4_5 | spl4_8 | spl4_5),
% 0.19/0.51    inference(avatar_split_clause,[],[f120,f91,f123,f91])).
% 0.19/0.51  fof(f91,plain,(
% 0.19/0.51    spl4_5 <=> v1_xboole_0(sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.51  fof(f120,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | r1_tarski(X0,X1) | v1_xboole_0(sK0)) ) | spl4_5),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f119])).
% 0.19/0.51  fof(f119,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X1,sK0) | r1_tarski(X0,X1) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) ) | spl4_5),
% 0.19/0.51    inference(resolution,[],[f118,f97])).
% 0.19/0.51  fof(f97,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f96,f51])).
% 0.19/0.51  fof(f96,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.19/0.51    inference(forward_demodulation,[],[f54,f51])).
% 0.19/0.51  fof(f54,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.19/0.51    inference(nnf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.19/0.51  fof(f118,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | spl4_5),
% 0.19/0.51    inference(resolution,[],[f117,f92])).
% 0.19/0.51  fof(f92,plain,(
% 0.19/0.51    ~v1_xboole_0(sK0) | spl4_5),
% 0.19/0.51    inference(avatar_component_clause,[],[f91])).
% 0.19/0.51  fof(f117,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~r1_orders_2(k2_yellow_1(X1),X2,X0) | r3_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1)) )),
% 0.19/0.51    inference(resolution,[],[f116,f53])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.19/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.19/0.51  fof(f116,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0)) )),
% 0.19/0.51    inference(global_subsumption,[],[f48,f115])).
% 0.19/0.51  fof(f115,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.19/0.51    inference(forward_demodulation,[],[f114,f51])).
% 0.19/0.51  fof(f114,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.19/0.51    inference(forward_demodulation,[],[f113,f51])).
% 0.19/0.51  fof(f113,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.19/0.51    inference(resolution,[],[f65,f50])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f42])).
% 0.19/0.51  fof(f42,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(nnf_transformation,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f110,plain,(
% 0.19/0.51    spl4_7 | ~spl4_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f106,f79,f108])).
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    spl4_2 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.51  fof(f106,plain,(
% 0.19/0.51    m1_subset_1(sK2,sK0) | ~spl4_2),
% 0.19/0.51    inference(forward_demodulation,[],[f80,f51])).
% 0.19/0.51  fof(f80,plain,(
% 0.19/0.51    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f79])).
% 0.19/0.51  fof(f105,plain,(
% 0.19/0.51    spl4_6 | ~spl4_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f101,f83,f103])).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    spl4_3 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.51  fof(f101,plain,(
% 0.19/0.51    m1_subset_1(sK1,sK0) | ~spl4_3),
% 0.19/0.51    inference(forward_demodulation,[],[f84,f51])).
% 0.19/0.51  fof(f84,plain,(
% 0.19/0.51    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f83])).
% 0.19/0.51  fof(f93,plain,(
% 0.19/0.51    ~spl4_5),
% 0.19/0.51    inference(avatar_split_clause,[],[f43,f91])).
% 0.19/0.51  fof(f43,plain,(
% 0.19/0.51    ~v1_xboole_0(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  fof(f35,plain,(
% 0.19/0.51    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f34,f33,f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.19/0.51    inference(flattening,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,negated_conjecture,(
% 0.19/0.51    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.19/0.51    inference(negated_conjecture,[],[f12])).
% 0.19/0.51  fof(f12,conjecture,(
% 0.19/0.51    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.19/0.51  fof(f89,plain,(
% 0.19/0.51    spl4_4),
% 0.19/0.51    inference(avatar_split_clause,[],[f44,f87])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    v2_lattice3(k2_yellow_1(sK0))),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    spl4_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f45,f83])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  fof(f81,plain,(
% 0.19/0.51    spl4_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f46,f79])).
% 0.19/0.51  fof(f46,plain,(
% 0.19/0.51    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    ~spl4_1),
% 0.19/0.51    inference(avatar_split_clause,[],[f69,f75])).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k1_setfam_1(k2_tarski(sK1,sK2)))),
% 0.19/0.51    inference(definition_unfolding,[],[f47,f63])).
% 0.19/0.51  fof(f47,plain,(
% 0.19/0.51    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.19/0.51    inference(cnf_transformation,[],[f35])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (25885)------------------------------
% 0.19/0.51  % (25885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (25885)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (25885)Memory used [KB]: 10874
% 0.19/0.51  % (25885)Time elapsed: 0.094 s
% 0.19/0.51  % (25885)------------------------------
% 0.19/0.51  % (25885)------------------------------
% 0.19/0.52  % (25865)Success in time 0.164 s
%------------------------------------------------------------------------------
