%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 289 expanded)
%              Number of leaves         :   31 ( 118 expanded)
%              Depth                    :   15
%              Number of atoms          :  701 (1273 expanded)
%              Number of equality atoms :   29 (  80 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f105,f110,f125,f140,f142,f150,f189,f207,f216,f357,f364,f387])).

fof(f387,plain,
    ( ~ spl4_43
    | spl4_22
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f383,f362,f214,f355])).

fof(f355,plain,
    ( spl4_43
  <=> r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f214,plain,
    ( spl4_22
  <=> r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f362,plain,
    ( spl4_44
  <=> r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f383,plain,
    ( ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_22
    | ~ spl4_44 ),
    inference(resolution,[],[f378,f215])).

fof(f215,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f214])).

fof(f378,plain,
    ( ! [X1] :
        ( r1_tarski(k2_xboole_0(X1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
        | ~ r1_tarski(X1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) )
    | ~ spl4_44 ),
    inference(resolution,[],[f363,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f363,plain,
    ( r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f362])).

fof(f364,plain,
    ( ~ spl4_9
    | ~ spl4_4
    | ~ spl4_10
    | spl4_44
    | ~ spl4_7
    | ~ spl4_6
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f360,f148,f108,f103,f103,f108,f362,f133,f87,f130])).

fof(f130,plain,
    ( spl4_9
  <=> v5_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f87,plain,
    ( spl4_4
  <=> v1_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f133,plain,
    ( spl4_10
  <=> l1_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f103,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f108,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f148,plain,
    ( spl4_12
  <=> ! [X3,X2,X4] :
        ( r1_tarski(X2,k13_lattice3(k2_yellow_1(sK0),X3,X4))
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(X4,sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k13_lattice3(k2_yellow_1(sK0),X3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f360,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f359,f53])).

fof(f53,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f359,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f349,f53])).

fof(f349,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f340,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f72,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_lattice3)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).

fof(f340,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
        | ~ m1_subset_1(X1,sK0)
        | r1_tarski(X1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) )
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f332,f109])).

fof(f109,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f332,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | r1_tarski(X0,k13_lattice3(k2_yellow_1(sK0),sK1,X1))
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k13_lattice3(k2_yellow_1(sK0),sK1,X1)) )
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f149,f104])).

fof(f104,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f149,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X3,sK0)
        | r1_tarski(X2,k13_lattice3(k2_yellow_1(sK0),X3,X4))
        | ~ m1_subset_1(X4,sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k13_lattice3(k2_yellow_1(sK0),X3,X4)) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f357,plain,
    ( ~ spl4_9
    | ~ spl4_4
    | ~ spl4_10
    | spl4_43
    | ~ spl4_7
    | ~ spl4_6
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f353,f148,f108,f103,f103,f108,f355,f133,f87,f130])).

fof(f353,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f351,f53])).

fof(f351,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK1,sK0)
    | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f348,f53])).

fof(f348,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f340,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f73,f68])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f216,plain,
    ( ~ spl4_22
    | spl4_1
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f212,f205,f75,f214])).

fof(f75,plain,
    ( spl4_1
  <=> r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f205,plain,
    ( spl4_20
  <=> k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f212,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_1
    | ~ spl4_20 ),
    inference(superposition,[],[f76,f206])).

fof(f206,plain,
    ( k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f205])).

fof(f76,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f207,plain,
    ( spl4_20
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f198,f187,f108,f103,f205])).

fof(f187,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,sK0)
        | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k13_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f198,plain,
    ( k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(resolution,[],[f190,f109])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k10_lattice3(k2_yellow_1(sK0),sK1,X0) = k13_lattice3(k2_yellow_1(sK0),sK1,X0) )
    | ~ spl4_6
    | ~ spl4_17 ),
    inference(resolution,[],[f188,f104])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k13_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f187])).

fof(f189,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | spl4_17
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f185,f87,f187,f133,f130])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k13_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f184,f53])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k13_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f183,f53])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k13_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f69,f88])).

fof(f88,plain,
    ( v1_lattice3(k2_yellow_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f150,plain,
    ( ~ spl4_4
    | spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f145,f123,f148,f87])).

fof(f123,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f145,plain,
    ( ! [X4,X2,X3] :
        ( r1_tarski(X2,k13_lattice3(k2_yellow_1(sK0),X3,X4))
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k13_lattice3(k2_yellow_1(sK0),X3,X4))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X4,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ v1_lattice3(k2_yellow_1(sK0)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f124,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0)) ) ),
    inference(global_subsumption,[],[f51,f52,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f68,f53])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | r1_tarski(X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f142,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f134,f52])).

fof(f134,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f140,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f131,f51])).

fof(f131,plain,
    ( ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f130])).

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
    inference(forward_demodulation,[],[f96,f53])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f56,f53])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(resolution,[],[f116,f55])).

fof(f55,plain,(
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
    inference(global_subsumption,[],[f50,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f114,f53])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f113,f53])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f67,f52])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f50,plain,(
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
    inference(forward_demodulation,[],[f80,f53])).

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
    inference(forward_demodulation,[],[f84,f53])).

fof(f84,plain,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f93,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f45,f91])).

fof(f45,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v1_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v1_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v1_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v1_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).

fof(f89,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f46,f87])).

fof(f46,plain,(
    v1_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f47,f83])).

fof(f47,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f48,f79])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f49,f75])).

fof(f49,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (26838)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (26822)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (26836)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (26834)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (26830)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (26828)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (26832)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (26823)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (26833)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (26832)Refutation not found, incomplete strategy% (26832)------------------------------
% 0.20/0.48  % (26832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26832)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (26832)Memory used [KB]: 6140
% 0.20/0.48  % (26832)Time elapsed: 0.084 s
% 0.20/0.48  % (26832)------------------------------
% 0.20/0.48  % (26832)------------------------------
% 0.20/0.48  % (26829)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (26827)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (26842)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (26826)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (26837)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (26837)Refutation not found, incomplete strategy% (26837)------------------------------
% 0.20/0.50  % (26837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (26824)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (26837)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (26837)Memory used [KB]: 6268
% 0.20/0.50  % (26837)Time elapsed: 0.096 s
% 0.20/0.50  % (26837)------------------------------
% 0.20/0.50  % (26837)------------------------------
% 0.20/0.50  % (26839)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (26825)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (26828)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f388,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f77,f81,f85,f89,f93,f105,f110,f125,f140,f142,f150,f189,f207,f216,f357,f364,f387])).
% 0.20/0.50  fof(f387,plain,(
% 0.20/0.50    ~spl4_43 | spl4_22 | ~spl4_44),
% 0.20/0.50    inference(avatar_split_clause,[],[f383,f362,f214,f355])).
% 0.20/0.50  fof(f355,plain,(
% 0.20/0.50    spl4_43 <=> r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    spl4_22 <=> r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    spl4_44 <=> r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.20/0.50  fof(f383,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (spl4_22 | ~spl4_44)),
% 0.20/0.50    inference(resolution,[],[f378,f215])).
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    ~r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f214])).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(k2_xboole_0(X1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(X1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))) ) | ~spl4_44),
% 0.20/0.50    inference(resolution,[],[f363,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.20/0.50  fof(f363,plain,(
% 0.20/0.50    r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~spl4_44),
% 0.20/0.50    inference(avatar_component_clause,[],[f362])).
% 0.20/0.50  fof(f364,plain,(
% 0.20/0.50    ~spl4_9 | ~spl4_4 | ~spl4_10 | spl4_44 | ~spl4_7 | ~spl4_6 | ~spl4_6 | ~spl4_7 | ~spl4_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f360,f148,f108,f103,f103,f108,f362,f133,f87,f130])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    spl4_9 <=> v5_orders_2(k2_yellow_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl4_4 <=> v1_lattice3(k2_yellow_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    spl4_10 <=> l1_orders_2(k2_yellow_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl4_6 <=> m1_subset_1(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl4_7 <=> m1_subset_1(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    spl4_12 <=> ! [X3,X2,X4] : (r1_tarski(X2,k13_lattice3(k2_yellow_1(sK0),X3,X4)) | ~m1_subset_1(X3,sK0) | ~m1_subset_1(X4,sK0) | ~m1_subset_1(X2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k13_lattice3(k2_yellow_1(sK0),X3,X4)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.50  fof(f360,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | (~spl4_6 | ~spl4_7 | ~spl4_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f359,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.50  fof(f359,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,sK0) | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | (~spl4_6 | ~spl4_7 | ~spl4_12)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f358])).
% 0.20/0.50  fof(f358,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK2,sK0) | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | (~spl4_6 | ~spl4_7 | ~spl4_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f349,f53])).
% 0.20/0.50  fof(f349,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,sK0) | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | (~spl4_6 | ~spl4_7 | ~spl4_12)),
% 0.20/0.50    inference(resolution,[],[f340,f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f72,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_lattice3)).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k13_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.50    inference(rectify,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).
% 0.20/0.50  fof(f340,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_orders_2(k2_yellow_1(sK0),X1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(X1,sK0) | r1_tarski(X1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))) ) | (~spl4_6 | ~spl4_7 | ~spl4_12)),
% 0.20/0.50    inference(resolution,[],[f332,f109])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    m1_subset_1(sK2,sK0) | ~spl4_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f108])).
% 0.20/0.50  fof(f332,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | r1_tarski(X0,k13_lattice3(k2_yellow_1(sK0),sK1,X1)) | ~m1_subset_1(X0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X0,k13_lattice3(k2_yellow_1(sK0),sK1,X1))) ) | (~spl4_6 | ~spl4_12)),
% 0.20/0.50    inference(resolution,[],[f149,f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    m1_subset_1(sK1,sK0) | ~spl4_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f103])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X4,X2,X3] : (~m1_subset_1(X3,sK0) | r1_tarski(X2,k13_lattice3(k2_yellow_1(sK0),X3,X4)) | ~m1_subset_1(X4,sK0) | ~m1_subset_1(X2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k13_lattice3(k2_yellow_1(sK0),X3,X4))) ) | ~spl4_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f148])).
% 0.20/0.50  fof(f357,plain,(
% 0.20/0.50    ~spl4_9 | ~spl4_4 | ~spl4_10 | spl4_43 | ~spl4_7 | ~spl4_6 | ~spl4_6 | ~spl4_7 | ~spl4_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f353,f148,f108,f103,f103,f108,f355,f133,f87,f130])).
% 0.20/0.50  fof(f353,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | (~spl4_6 | ~spl4_7 | ~spl4_12)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f352])).
% 0.20/0.50  fof(f352,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | (~spl4_6 | ~spl4_7 | ~spl4_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f351,f53])).
% 0.20/0.50  fof(f351,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK1,sK0) | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | (~spl4_6 | ~spl4_7 | ~spl4_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f348,f53])).
% 0.20/0.50  fof(f348,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,sK0) | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | (~spl4_6 | ~spl4_7 | ~spl4_12)),
% 0.20/0.50    inference(resolution,[],[f340,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f73,f68])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    ~spl4_22 | spl4_1 | ~spl4_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f212,f205,f75,f214])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl4_1 <=> r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    spl4_20 <=> k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    ~r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | (spl4_1 | ~spl4_20)),
% 0.20/0.50    inference(superposition,[],[f76,f206])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~spl4_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f205])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f75])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    spl4_20 | ~spl4_6 | ~spl4_7 | ~spl4_17),
% 0.20/0.50    inference(avatar_split_clause,[],[f198,f187,f108,f103,f205])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    spl4_17 <=> ! [X1,X0] : (~m1_subset_1(X1,sK0) | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k13_lattice3(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X0,sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK1,sK2) | (~spl4_6 | ~spl4_7 | ~spl4_17)),
% 0.20/0.50    inference(resolution,[],[f190,f109])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,sK0) | k10_lattice3(k2_yellow_1(sK0),sK1,X0) = k13_lattice3(k2_yellow_1(sK0),sK1,X0)) ) | (~spl4_6 | ~spl4_17)),
% 0.20/0.50    inference(resolution,[],[f188,f104])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k13_lattice3(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X0,sK0)) ) | ~spl4_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f187])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    ~spl4_9 | ~spl4_10 | spl4_17 | ~spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f185,f87,f187,f133,f130])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~l1_orders_2(k2_yellow_1(sK0)) | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k13_lattice3(k2_yellow_1(sK0),X1,X0) | ~v5_orders_2(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.20/0.50    inference(forward_demodulation,[],[f184,f53])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k13_lattice3(k2_yellow_1(sK0),X1,X0) | ~v5_orders_2(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.20/0.50    inference(forward_demodulation,[],[f183,f53])).
% 0.20/0.50  fof(f183,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | k10_lattice3(k2_yellow_1(sK0),X1,X0) = k13_lattice3(k2_yellow_1(sK0),X1,X0) | ~v5_orders_2(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.20/0.50    inference(resolution,[],[f69,f88])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    v1_lattice3(k2_yellow_1(sK0)) | ~spl4_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f87])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~v5_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    ~spl4_4 | spl4_12 | ~spl4_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f145,f123,f148,f87])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    spl4_8 <=> ! [X1,X0] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | r1_tarski(X0,X1) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    ( ! [X4,X2,X3] : (r1_tarski(X2,k13_lattice3(k2_yellow_1(sK0),X3,X4)) | ~r1_orders_2(k2_yellow_1(sK0),X2,k13_lattice3(k2_yellow_1(sK0),X3,X4)) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X4,sK0) | ~m1_subset_1(X3,sK0) | ~v1_lattice3(k2_yellow_1(sK0))) ) | ~spl4_8),
% 0.20/0.50    inference(resolution,[],[f124,f112])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0))) )),
% 0.20/0.50    inference(global_subsumption,[],[f51,f52,f111])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v1_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.50    inference(superposition,[],[f68,f53])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | r1_tarski(X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0)) ) | ~spl4_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f123])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    spl4_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f141])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    $false | spl4_10),
% 0.20/0.50    inference(resolution,[],[f134,f52])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ~l1_orders_2(k2_yellow_1(sK0)) | spl4_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f133])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    spl4_9),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f139])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    $false | spl4_9),
% 0.20/0.50    inference(resolution,[],[f131,f51])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ~v5_orders_2(k2_yellow_1(sK0)) | spl4_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f130])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    spl4_5 | spl4_8 | spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f120,f91,f123,f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    spl4_5 <=> v1_xboole_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | r1_tarski(X0,X1) | v1_xboole_0(sK0)) ) | spl4_5),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X1,sK0) | r1_tarski(X0,X1) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) ) | spl4_5),
% 0.20/0.50    inference(resolution,[],[f118,f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f96,f53])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f56,f53])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | spl4_5),
% 0.20/0.50    inference(resolution,[],[f117,f92])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0) | spl4_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f91])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~r1_orders_2(k2_yellow_1(X1),X2,X0) | r3_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f116,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.50    inference(global_subsumption,[],[f50,f115])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f114,f53])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f113,f53])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.50    inference(resolution,[],[f67,f52])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    spl4_7 | ~spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f106,f79,f108])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl4_2 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    m1_subset_1(sK2,sK0) | ~spl4_2),
% 0.20/0.50    inference(forward_demodulation,[],[f80,f53])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f79])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    spl4_6 | ~spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f101,f83,f103])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl4_3 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    m1_subset_1(sK1,sK0) | ~spl4_3),
% 0.20/0.50    inference(forward_demodulation,[],[f84,f53])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f83])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ~spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f45,f91])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ((~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v1_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f36,f35,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v1_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ? [X2] : (~r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f46,f87])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    v1_lattice3(k2_yellow_1(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f47,f83])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f48,f79])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ~spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f49,f75])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (26828)------------------------------
% 0.20/0.50  % (26828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (26828)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (26828)Memory used [KB]: 11001
% 0.20/0.50  % (26828)Time elapsed: 0.054 s
% 0.20/0.50  % (26828)------------------------------
% 0.20/0.50  % (26828)------------------------------
% 0.20/0.50  % (26835)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (26821)Success in time 0.152 s
%------------------------------------------------------------------------------
