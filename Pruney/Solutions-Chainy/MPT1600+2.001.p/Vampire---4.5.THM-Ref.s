%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:32 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 497 expanded)
%              Number of leaves         :   42 ( 205 expanded)
%              Depth                    :   22
%              Number of atoms          : 1198 (2564 expanded)
%              Number of equality atoms :   95 ( 293 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f99,f104,f210,f212,f257,f260,f276,f278,f518,f637,f663,f716,f719,f728,f1006,f1013,f1027,f1042,f1052,f1065,f1084,f1105])).

fof(f1105,plain,
    ( ~ spl4_51
    | ~ spl4_13
    | ~ spl4_27
    | ~ spl4_35
    | spl4_1
    | ~ spl4_20
    | ~ spl4_7
    | ~ spl4_6
    | spl4_106 ),
    inference(avatar_split_clause,[],[f1104,f1081,f97,f102,f268,f72,f363,f313,f203,f500])).

fof(f500,plain,
    ( spl4_51
  <=> v5_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f203,plain,
    ( spl4_13
  <=> l1_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f313,plain,
    ( spl4_27
  <=> r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f363,plain,
    ( spl4_35
  <=> r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f72,plain,
    ( spl4_1
  <=> k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f268,plain,
    ( spl4_20
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f102,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f97,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1081,plain,
    ( spl4_106
  <=> r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f1104,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_106 ),
    inference(forward_demodulation,[],[f1103,f46])).

fof(f46,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f1103,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_106 ),
    inference(forward_demodulation,[],[f1102,f46])).

fof(f1102,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_106 ),
    inference(forward_demodulation,[],[f1099,f46])).

fof(f1099,plain,
    ( k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_106 ),
    inference(resolution,[],[f1082,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
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
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f35])).

fof(f35,plain,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
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
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
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
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X5)
                                & r1_orders_2(X0,X1,X5) )
                             => r1_orders_2(X0,X3,X5) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_0)).

fof(f1082,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2)))
    | spl4_106 ),
    inference(avatar_component_clause,[],[f1081])).

fof(f1084,plain,
    ( ~ spl4_51
    | ~ spl4_13
    | ~ spl4_27
    | ~ spl4_106
    | spl4_1
    | ~ spl4_35
    | ~ spl4_20
    | ~ spl4_7
    | ~ spl4_6
    | ~ spl4_104 ),
    inference(avatar_split_clause,[],[f1079,f1063,f97,f102,f268,f363,f72,f1081,f313,f203,f500])).

fof(f1063,plain,
    ( spl4_104
  <=> ! [X0] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,X0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f1079,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_104 ),
    inference(forward_demodulation,[],[f1078,f46])).

fof(f1078,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_104 ),
    inference(duplicate_literal_removal,[],[f1077])).

fof(f1077,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_104 ),
    inference(forward_demodulation,[],[f1076,f46])).

fof(f1076,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_104 ),
    inference(forward_demodulation,[],[f1075,f46])).

fof(f1075,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2)))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_104 ),
    inference(duplicate_literal_removal,[],[f1071])).

fof(f1071,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,sK0)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2)))
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    | ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | ~ spl4_104 ),
    inference(resolution,[],[f1064,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1064,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,X0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2))) )
    | ~ spl4_104 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f1065,plain,
    ( ~ spl4_27
    | spl4_104
    | ~ spl4_6
    | ~ spl4_102 ),
    inference(avatar_split_clause,[],[f1057,f1050,f97,f1063,f313])).

fof(f1050,plain,
    ( spl4_102
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f1057,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,X0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) )
    | ~ spl4_6
    | ~ spl4_102 ),
    inference(resolution,[],[f1051,f98])).

fof(f98,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f1051,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) )
    | ~ spl4_102 ),
    inference(avatar_component_clause,[],[f1050])).

fof(f1052,plain,
    ( ~ spl4_20
    | spl4_102
    | ~ spl4_101 ),
    inference(avatar_split_clause,[],[f1048,f1040,f1050,f268])).

fof(f1040,plain,
    ( spl4_101
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).

fof(f1048,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0) )
    | ~ spl4_101 ),
    inference(duplicate_literal_removal,[],[f1044])).

fof(f1044,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl4_101 ),
    inference(resolution,[],[f1041,f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(k2_yellow_1(X0),X1,X2,X3),X0)
      | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X3)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f44,f45,f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(k2_yellow_1(X0),X1,X2,X3),X0)
      | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X3)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f54,f46])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f45,plain,(
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

fof(f44,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
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

fof(f1041,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) )
    | ~ spl4_101 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f1042,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_13
    | spl4_101
    | ~ spl4_6
    | ~ spl4_99 ),
    inference(avatar_split_clause,[],[f1038,f1025,f97,f1040,f203,f200,f197])).

fof(f197,plain,
    ( spl4_11
  <=> v2_struct_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f200,plain,
    ( spl4_12
  <=> v3_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1025,plain,
    ( spl4_99
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2)
        | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f1038,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK1,sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_99 ),
    inference(forward_demodulation,[],[f1037,f46])).

fof(f1037,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_99 ),
    inference(duplicate_literal_removal,[],[f1036])).

fof(f1036,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_99 ),
    inference(forward_demodulation,[],[f1030,f46])).

fof(f1030,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | ~ r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_99 ),
    inference(resolution,[],[f1026,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f1026,plain,
    ( ! [X2,X3] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) )
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f1027,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_13
    | spl4_99
    | ~ spl4_7
    | ~ spl4_97 ),
    inference(avatar_split_clause,[],[f1023,f1011,f102,f1025,f203,f200,f197])).

fof(f1011,plain,
    ( spl4_97
  <=> ! [X1,X0] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))
        | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).

fof(f1023,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2,sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))
        | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_97 ),
    inference(forward_demodulation,[],[f1022,f46])).

fof(f1022,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))
        | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_97 ),
    inference(duplicate_literal_removal,[],[f1021])).

fof(f1021,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))
        | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_97 ),
    inference(forward_demodulation,[],[f1015,f46])).

fof(f1015,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))
        | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X3,sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | v2_struct_0(k2_yellow_1(sK0)) )
    | ~ spl4_97 ),
    inference(resolution,[],[f1012,f66])).

fof(f1012,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))
        | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0) )
    | ~ spl4_97 ),
    inference(avatar_component_clause,[],[f1011])).

fof(f1013,plain,
    ( ~ spl4_6
    | spl4_97
    | spl4_5
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f1009,f1004,f88,f1011,f97])).

fof(f88,plain,
    ( spl4_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1004,plain,
    ( spl4_96
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))
        | ~ r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0)
        | ~ r1_tarski(sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f1009,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(sK1,sK0)
        | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) )
    | spl4_5
    | ~ spl4_96 ),
    inference(duplicate_literal_removal,[],[f1008])).

fof(f1008,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK1,sK0)
        | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) )
    | spl4_5
    | ~ spl4_96 ),
    inference(resolution,[],[f1007,f89])).

fof(f89,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f1007,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X2)
        | ~ r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)),X2)
        | ~ m1_subset_1(sK1,X2)
        | ~ r3_orders_2(k2_yellow_1(X2),sK1,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) )
    | ~ spl4_96 ),
    inference(resolution,[],[f1005,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f93,f46])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f49,f46])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f1005,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))
        | ~ r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) )
    | ~ spl4_96 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f1006,plain,
    ( ~ spl4_7
    | spl4_96
    | ~ spl4_2
    | spl4_5
    | ~ spl4_73 ),
    inference(avatar_split_clause,[],[f1002,f726,f88,f76,f1004,f102])).

fof(f76,plain,
    ( spl4_2
  <=> r2_hidden(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f726,plain,
    ( spl4_73
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ r1_tarski(X1,sK3(k2_yellow_1(sK0),X2,X0,X1))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X0,X1),sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X2,sK0)
        | k10_lattice3(k2_yellow_1(sK0),X2,X0) = X1
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f1002,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_tarski(sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK2,sK0)
        | ~ r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) )
    | ~ spl4_2
    | spl4_5
    | ~ spl4_73 ),
    inference(duplicate_literal_removal,[],[f1001])).

fof(f1001,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_tarski(sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK2,sK0)
        | ~ r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) )
    | ~ spl4_2
    | spl4_5
    | ~ spl4_73 ),
    inference(resolution,[],[f954,f89])).

fof(f954,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(X1,sK0)
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(sK1,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)),sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)),X2)
        | ~ m1_subset_1(sK2,X2)
        | ~ r3_orders_2(k2_yellow_1(X2),sK2,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) )
    | ~ spl4_2
    | ~ spl4_73 ),
    inference(resolution,[],[f951,f94])).

fof(f951,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X1,sK0)
        | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(sK1,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)),sK0) )
    | ~ spl4_2
    | ~ spl4_73 ),
    inference(resolution,[],[f948,f77])).

fof(f77,plain,
    ( r2_hidden(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f948,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k2_xboole_0(X2,X3),sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(X2,X3))
        | ~ m1_subset_1(X0,sK0)
        | k2_xboole_0(X2,X3) = k10_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(X2,X3))
        | ~ r1_tarski(X3,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(X2,X3)))
        | ~ r1_tarski(X2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(X2,X3)))
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(X2,X3)),sK0) )
    | ~ spl4_73 ),
    inference(resolution,[],[f807,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f807,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k2_xboole_0(X1,X2),sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X3,X0,k2_xboole_0(X1,X2)),sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(X1,X2))
        | ~ m1_subset_1(X3,sK0)
        | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(sK0),X3,X0)
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X2,sK3(k2_yellow_1(sK0),X3,X0,k2_xboole_0(X1,X2)))
        | ~ r1_tarski(X1,sK3(k2_yellow_1(sK0),X3,X0,k2_xboole_0(X1,X2))) )
    | ~ spl4_73 ),
    inference(resolution,[],[f727,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f727,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,sK3(k2_yellow_1(sK0),X2,X0,X1))
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X0,X1),sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X2,sK0)
        | k10_lattice3(k2_yellow_1(sK0),X2,X0) = X1
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,X1) )
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f726])).

fof(f728,plain,
    ( spl4_5
    | spl4_73
    | spl4_5 ),
    inference(avatar_split_clause,[],[f724,f88,f726,f88])).

fof(f724,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,X1)
        | k10_lattice3(k2_yellow_1(sK0),X2,X0) = X1
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X0,X1),sK0)
        | ~ r1_tarski(X1,sK3(k2_yellow_1(sK0),X2,X0,X1))
        | v1_xboole_0(sK0) )
    | spl4_5 ),
    inference(duplicate_literal_removal,[],[f722])).

fof(f722,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ r1_orders_2(k2_yellow_1(sK0),X2,X1)
        | k10_lattice3(k2_yellow_1(sK0),X2,X0) = X1
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK3(k2_yellow_1(sK0),X2,X0,X1),sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_tarski(X1,sK3(k2_yellow_1(sK0),X2,X0,X1))
        | v1_xboole_0(sK0) )
    | spl4_5 ),
    inference(resolution,[],[f569,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f91,f46])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f50,f46])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f569,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),X2,sK3(k2_yellow_1(sK0),X0,X1,X2))
        | ~ r1_orders_2(k2_yellow_1(sK0),X1,X2)
        | ~ r1_orders_2(k2_yellow_1(sK0),X0,X2)
        | k10_lattice3(k2_yellow_1(sK0),X0,X1) = X2
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X2,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | spl4_5 ),
    inference(resolution,[],[f413,f89])).

fof(f413,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X3)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X3)
      | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
      | ~ r3_orders_2(k2_yellow_1(X0),X3,sK3(k2_yellow_1(X0),X1,X2,X3))
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(global_subsumption,[],[f44,f45,f132,f412])).

fof(f412,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3(k2_yellow_1(X0),X1,X2,X3),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X3)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X3)
      | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3
      | ~ r3_orders_2(k2_yellow_1(X0),X3,sK3(k2_yellow_1(X0),X1,X2,X3))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f161,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f161,plain,(
    ! [X14,X12,X15,X13] :
      ( v2_struct_0(k2_yellow_1(X13))
      | ~ m1_subset_1(sK3(k2_yellow_1(X13),X15,X12,X14),X13)
      | ~ m1_subset_1(X12,X13)
      | ~ m1_subset_1(X15,X13)
      | ~ r1_orders_2(k2_yellow_1(X13),X12,X14)
      | ~ r1_orders_2(k2_yellow_1(X13),X15,X14)
      | k10_lattice3(k2_yellow_1(X13),X15,X12) = X14
      | ~ r3_orders_2(k2_yellow_1(X13),X14,sK3(k2_yellow_1(X13),X15,X12,X14))
      | ~ m1_subset_1(X14,X13) ) ),
    inference(global_subsumption,[],[f43,f45,f160])).

fof(f160,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(X14,X13)
      | ~ m1_subset_1(sK3(k2_yellow_1(X13),X15,X12,X14),X13)
      | ~ m1_subset_1(X12,X13)
      | ~ m1_subset_1(X15,X13)
      | ~ r1_orders_2(k2_yellow_1(X13),X12,X14)
      | ~ r1_orders_2(k2_yellow_1(X13),X15,X14)
      | k10_lattice3(k2_yellow_1(X13),X15,X12) = X14
      | ~ r3_orders_2(k2_yellow_1(X13),X14,sK3(k2_yellow_1(X13),X15,X12,X14))
      | ~ l1_orders_2(k2_yellow_1(X13))
      | ~ v3_orders_2(k2_yellow_1(X13))
      | v2_struct_0(k2_yellow_1(X13)) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(X14,X13)
      | ~ m1_subset_1(sK3(k2_yellow_1(X13),X15,X12,X14),X13)
      | ~ m1_subset_1(X12,X13)
      | ~ m1_subset_1(X14,X13)
      | ~ m1_subset_1(X15,X13)
      | ~ r1_orders_2(k2_yellow_1(X13),X12,X14)
      | ~ r1_orders_2(k2_yellow_1(X13),X15,X14)
      | k10_lattice3(k2_yellow_1(X13),X15,X12) = X14
      | ~ r3_orders_2(k2_yellow_1(X13),X14,sK3(k2_yellow_1(X13),X15,X12,X14))
      | ~ l1_orders_2(k2_yellow_1(X13))
      | ~ v3_orders_2(k2_yellow_1(X13))
      | v2_struct_0(k2_yellow_1(X13)) ) ),
    inference(forward_demodulation,[],[f158,f46])).

fof(f158,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(sK3(k2_yellow_1(X13),X15,X12,X14),X13)
      | ~ m1_subset_1(X12,X13)
      | ~ m1_subset_1(X14,X13)
      | ~ m1_subset_1(X15,X13)
      | ~ r1_orders_2(k2_yellow_1(X13),X12,X14)
      | ~ r1_orders_2(k2_yellow_1(X13),X15,X14)
      | k10_lattice3(k2_yellow_1(X13),X15,X12) = X14
      | ~ r3_orders_2(k2_yellow_1(X13),X14,sK3(k2_yellow_1(X13),X15,X12,X14))
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(X13)))
      | ~ l1_orders_2(k2_yellow_1(X13))
      | ~ v3_orders_2(k2_yellow_1(X13))
      | v2_struct_0(k2_yellow_1(X13)) ) ),
    inference(forward_demodulation,[],[f143,f46])).

fof(f143,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(X12,X13)
      | ~ m1_subset_1(X14,X13)
      | ~ m1_subset_1(X15,X13)
      | ~ r1_orders_2(k2_yellow_1(X13),X12,X14)
      | ~ r1_orders_2(k2_yellow_1(X13),X15,X14)
      | k10_lattice3(k2_yellow_1(X13),X15,X12) = X14
      | ~ r3_orders_2(k2_yellow_1(X13),X14,sK3(k2_yellow_1(X13),X15,X12,X14))
      | ~ m1_subset_1(sK3(k2_yellow_1(X13),X15,X12,X14),u1_struct_0(k2_yellow_1(X13)))
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(X13)))
      | ~ l1_orders_2(k2_yellow_1(X13))
      | ~ v3_orders_2(k2_yellow_1(X13))
      | v2_struct_0(k2_yellow_1(X13)) ) ),
    inference(resolution,[],[f138,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,sK3(k2_yellow_1(X0),X2,X3,X1))
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X3,X1)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | k10_lattice3(k2_yellow_1(X0),X2,X3) = X1 ) ),
    inference(global_subsumption,[],[f45,f137])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,sK3(k2_yellow_1(X0),X2,X3,X1))
      | ~ r1_orders_2(k2_yellow_1(X0),X3,X1)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | k10_lattice3(k2_yellow_1(X0),X2,X3) = X1 ) ),
    inference(forward_demodulation,[],[f136,f46])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,sK3(k2_yellow_1(X0),X2,X3,X1))
      | ~ r1_orders_2(k2_yellow_1(X0),X3,X1)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | k10_lattice3(k2_yellow_1(X0),X2,X3) = X1 ) ),
    inference(forward_demodulation,[],[f135,f46])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,sK3(k2_yellow_1(X0),X2,X3,X1))
      | ~ r1_orders_2(k2_yellow_1(X0),X3,X1)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | k10_lattice3(k2_yellow_1(X0),X2,X3) = X1 ) ),
    inference(forward_demodulation,[],[f134,f46])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,sK3(k2_yellow_1(X0),X2,X3,X1))
      | ~ r1_orders_2(k2_yellow_1(X0),X3,X1)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | k10_lattice3(k2_yellow_1(X0),X2,X3) = X1 ) ),
    inference(resolution,[],[f57,f44])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f719,plain,
    ( spl4_5
    | ~ spl4_18
    | ~ spl4_7
    | ~ spl4_20
    | spl4_72 ),
    inference(avatar_split_clause,[],[f717,f714,f268,f102,f249,f88])).

fof(f249,plain,
    ( spl4_18
  <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f714,plain,
    ( spl4_72
  <=> r3_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f717,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | v1_xboole_0(sK0)
    | spl4_72 ),
    inference(resolution,[],[f715,f92])).

fof(f715,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | spl4_72 ),
    inference(avatar_component_clause,[],[f714])).

fof(f716,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_72
    | ~ spl4_20
    | ~ spl4_7
    | spl4_35 ),
    inference(avatar_split_clause,[],[f712,f363,f102,f268,f714,f203,f200,f197])).

fof(f712,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_35 ),
    inference(forward_demodulation,[],[f711,f46])).

fof(f711,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_35 ),
    inference(forward_demodulation,[],[f710,f46])).

fof(f710,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_35 ),
    inference(resolution,[],[f685,f65])).

fof(f685,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f363])).

fof(f663,plain,
    ( spl4_5
    | ~ spl4_17
    | ~ spl4_6
    | ~ spl4_20
    | spl4_66 ),
    inference(avatar_split_clause,[],[f661,f635,f268,f97,f246,f88])).

fof(f246,plain,
    ( spl4_17
  <=> r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f635,plain,
    ( spl4_66
  <=> r3_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f661,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | v1_xboole_0(sK0)
    | spl4_66 ),
    inference(resolution,[],[f636,f92])).

fof(f636,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | spl4_66 ),
    inference(avatar_component_clause,[],[f635])).

fof(f637,plain,
    ( spl4_11
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_66
    | ~ spl4_20
    | ~ spl4_6
    | spl4_27 ),
    inference(avatar_split_clause,[],[f633,f313,f97,f268,f635,f203,f200,f197])).

fof(f633,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_27 ),
    inference(forward_demodulation,[],[f632,f46])).

fof(f632,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_27 ),
    inference(forward_demodulation,[],[f631,f46])).

fof(f631,plain,
    ( ~ r3_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | spl4_27 ),
    inference(resolution,[],[f606,f65])).

fof(f606,plain,
    ( ~ r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f313])).

fof(f518,plain,(
    spl4_51 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | spl4_51 ),
    inference(resolution,[],[f501,f44])).

fof(f501,plain,
    ( ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_51 ),
    inference(avatar_component_clause,[],[f500])).

fof(f278,plain,
    ( spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f277,f197,f88])).

fof(f277,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f198,f48])).

fof(f198,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f197])).

fof(f276,plain,
    ( ~ spl4_2
    | spl4_20 ),
    inference(avatar_split_clause,[],[f274,f268,f76])).

fof(f274,plain,
    ( ~ r2_hidden(k2_xboole_0(sK1,sK2),sK0)
    | spl4_20 ),
    inference(resolution,[],[f269,f64])).

fof(f269,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),sK0)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f268])).

fof(f260,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl4_18 ),
    inference(resolution,[],[f250,f105])).

fof(f105,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f62,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f250,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f249])).

fof(f257,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl4_17 ),
    inference(resolution,[],[f247,f62])).

fof(f247,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f246])).

fof(f212,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f204,f45])).

fof(f204,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f210,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f201,f43])).

fof(f201,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f200])).

fof(f104,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f100,f80,f102])).

fof(f80,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f100,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f81,f46])).

fof(f81,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f99,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f95,f84,f97])).

fof(f84,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f95,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f85,f46])).

fof(f85,plain,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f90,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f38,f88])).

fof(f38,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k2_xboole_0(sK1,sK2) != k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
    & r2_hidden(k2_xboole_0(sK1,sK2),sK0)
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2)
                & r2_hidden(k2_xboole_0(X1,X2),X0)
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(sK0),X1,X2)
              & r2_hidden(k2_xboole_0(X1,X2),sK0)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(sK0),X1,X2)
            & r2_hidden(k2_xboole_0(X1,X2),sK0)
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( k2_xboole_0(sK1,X2) != k10_lattice3(k2_yellow_1(sK0),sK1,X2)
          & r2_hidden(k2_xboole_0(sK1,X2),sK0)
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( k2_xboole_0(sK1,X2) != k10_lattice3(k2_yellow_1(sK0),sK1,X2)
        & r2_hidden(k2_xboole_0(sK1,X2),sK0)
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( k2_xboole_0(sK1,sK2) != k10_lattice3(k2_yellow_1(sK0),sK1,sK2)
      & r2_hidden(k2_xboole_0(sK1,sK2),sK0)
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2)
              & r2_hidden(k2_xboole_0(X1,X2),X0)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2)
              & r2_hidden(k2_xboole_0(X1,X2),X0)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => ( r2_hidden(k2_xboole_0(X1,X2),X0)
                 => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k2_xboole_0(X1,X2),X0)
               => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).

fof(f86,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f84])).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    r2_hidden(k2_xboole_0(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f42,f72])).

fof(f42,plain,(
    k2_xboole_0(sK1,sK2) != k10_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (11668)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (11683)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (11668)Refutation not found, incomplete strategy% (11668)------------------------------
% 0.21/0.47  % (11668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11668)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (11668)Memory used [KB]: 6140
% 0.21/0.47  % (11668)Time elapsed: 0.060 s
% 0.21/0.47  % (11668)------------------------------
% 0.21/0.47  % (11668)------------------------------
% 0.21/0.47  % (11684)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (11676)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (11684)Refutation not found, incomplete strategy% (11684)------------------------------
% 0.21/0.47  % (11684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11684)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (11684)Memory used [KB]: 6140
% 0.21/0.47  % (11684)Time elapsed: 0.007 s
% 0.21/0.47  % (11684)------------------------------
% 0.21/0.47  % (11684)------------------------------
% 0.21/0.48  % (11669)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (11669)Refutation not found, incomplete strategy% (11669)------------------------------
% 0.21/0.48  % (11669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (11669)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (11669)Memory used [KB]: 10618
% 0.21/0.48  % (11669)Time elapsed: 0.075 s
% 0.21/0.48  % (11669)------------------------------
% 0.21/0.48  % (11669)------------------------------
% 0.21/0.48  % (11675)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (11671)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (11670)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (11682)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (11682)Refutation not found, incomplete strategy% (11682)------------------------------
% 0.21/0.49  % (11682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11682)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11682)Memory used [KB]: 1663
% 0.21/0.49  % (11682)Time elapsed: 0.092 s
% 0.21/0.49  % (11682)------------------------------
% 0.21/0.49  % (11682)------------------------------
% 0.21/0.49  % (11674)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (11680)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (11680)Refutation not found, incomplete strategy% (11680)------------------------------
% 0.21/0.49  % (11680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11680)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11680)Memory used [KB]: 10618
% 0.21/0.49  % (11680)Time elapsed: 0.089 s
% 0.21/0.49  % (11680)------------------------------
% 0.21/0.49  % (11680)------------------------------
% 0.21/0.49  % (11687)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (11677)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (11672)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (11679)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (11679)Refutation not found, incomplete strategy% (11679)------------------------------
% 0.21/0.50  % (11679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11679)Memory used [KB]: 6012
% 0.21/0.50  % (11679)Time elapsed: 0.100 s
% 0.21/0.50  % (11679)------------------------------
% 0.21/0.50  % (11679)------------------------------
% 0.21/0.50  % (11685)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (11689)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (11678)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (11689)Refutation not found, incomplete strategy% (11689)------------------------------
% 0.21/0.51  % (11689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11689)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11689)Memory used [KB]: 10618
% 0.21/0.51  % (11689)Time elapsed: 0.106 s
% 0.21/0.51  % (11689)------------------------------
% 0.21/0.51  % (11689)------------------------------
% 0.21/0.51  % (11681)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (11688)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (11686)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.40/0.54  % (11675)Refutation found. Thanks to Tanya!
% 1.40/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f1119,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f99,f104,f210,f212,f257,f260,f276,f278,f518,f637,f663,f716,f719,f728,f1006,f1013,f1027,f1042,f1052,f1065,f1084,f1105])).
% 1.40/0.54  fof(f1105,plain,(
% 1.40/0.54    ~spl4_51 | ~spl4_13 | ~spl4_27 | ~spl4_35 | spl4_1 | ~spl4_20 | ~spl4_7 | ~spl4_6 | spl4_106),
% 1.40/0.54    inference(avatar_split_clause,[],[f1104,f1081,f97,f102,f268,f72,f363,f313,f203,f500])).
% 1.40/0.54  fof(f500,plain,(
% 1.40/0.54    spl4_51 <=> v5_orders_2(k2_yellow_1(sK0))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.40/0.54  fof(f203,plain,(
% 1.40/0.54    spl4_13 <=> l1_orders_2(k2_yellow_1(sK0))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.40/0.54  fof(f313,plain,(
% 1.40/0.54    spl4_27 <=> r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.54/0.54  fof(f363,plain,(
% 1.54/0.54    spl4_35 <=> r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))),
% 1.54/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.54/0.54  fof(f72,plain,(
% 1.54/0.54    spl4_1 <=> k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2)),
% 1.54/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.54/0.54  fof(f268,plain,(
% 1.54/0.54    spl4_20 <=> m1_subset_1(k2_xboole_0(sK1,sK2),sK0)),
% 1.54/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.54/0.54  fof(f102,plain,(
% 1.54/0.54    spl4_7 <=> m1_subset_1(sK2,sK0)),
% 1.54/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.54/0.54  fof(f97,plain,(
% 1.54/0.54    spl4_6 <=> m1_subset_1(sK1,sK0)),
% 1.54/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.54/0.54  fof(f1081,plain,(
% 1.54/0.54    spl4_106 <=> r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2)))),
% 1.54/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).
% 1.54/0.54  fof(f1104,plain,(
% 1.54/0.54    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | spl4_106),
% 1.54/0.54    inference(forward_demodulation,[],[f1103,f46])).
% 1.54/0.54  fof(f46,plain,(
% 1.54/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.54/0.54    inference(cnf_transformation,[],[f10])).
% 1.54/0.54  fof(f10,axiom,(
% 1.54/0.54    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.54/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 1.54/0.54  fof(f1103,plain,(
% 1.54/0.54    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | spl4_106),
% 1.54/0.54    inference(forward_demodulation,[],[f1102,f46])).
% 1.54/0.54  fof(f1102,plain,(
% 1.54/0.54    ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | spl4_106),
% 1.54/0.54    inference(forward_demodulation,[],[f1099,f46])).
% 1.54/0.54  fof(f1099,plain,(
% 1.54/0.54    k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | spl4_106),
% 1.54/0.54    inference(resolution,[],[f1082,f55])).
% 1.54/0.54  fof(f55,plain,(
% 1.54/0.54    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.54/0.54    inference(cnf_transformation,[],[f36])).
% 1.54/0.55  fof(f36,plain,(
% 1.54/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | ~r1_yellow_0(X0,k2_tarski(X1,X2)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.54/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f35])).
% 1.54/0.55  fof(f35,plain,(
% 1.54/0.55    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 1.54/0.55    introduced(choice_axiom,[])).
% 1.54/0.55  fof(f24,plain,(
% 1.54/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | ~r1_yellow_0(X0,k2_tarski(X1,X2)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.54/0.55    inference(flattening,[],[f23])).
% 1.54/0.55  fof(f23,plain,(
% 1.54/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) | (? [X4] : ((~r1_orders_2(X0,X3,X4) & (r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4))) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X5] : ((r1_orders_2(X0,X3,X5) | (~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5))) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | (~r1_yellow_0(X0,k2_tarski(X1,X2)) | k10_lattice3(X0,X1,X2) != X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.54/0.55    inference(ennf_transformation,[],[f14])).
% 1.54/0.55  fof(f14,plain,(
% 1.54/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) => (r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3)) & ((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) => (! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X5) & r1_orders_2(X0,X1,X5)) => r1_orders_2(X0,X3,X5))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))))))))),
% 1.54/0.55    inference(rectify,[],[f6])).
% 1.54/0.55  fof(f6,axiom,(
% 1.54/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) => (r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3)) & ((r1_yellow_0(X0,k2_tarski(X1,X2)) & k10_lattice3(X0,X1,X2) = X3) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))))))))),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_0)).
% 1.54/0.55  fof(f1082,plain,(
% 1.54/0.55    ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2))) | spl4_106),
% 1.54/0.55    inference(avatar_component_clause,[],[f1081])).
% 1.54/0.55  fof(f1084,plain,(
% 1.54/0.55    ~spl4_51 | ~spl4_13 | ~spl4_27 | ~spl4_106 | spl4_1 | ~spl4_35 | ~spl4_20 | ~spl4_7 | ~spl4_6 | ~spl4_104),
% 1.54/0.55    inference(avatar_split_clause,[],[f1079,f1063,f97,f102,f268,f363,f72,f1081,f313,f203,f500])).
% 1.54/0.55  fof(f1063,plain,(
% 1.54/0.55    spl4_104 <=> ! [X0] : (~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,X0) | ~m1_subset_1(X0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2))))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).
% 1.54/0.55  fof(f1079,plain,(
% 1.54/0.55    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~spl4_104),
% 1.54/0.55    inference(forward_demodulation,[],[f1078,f46])).
% 1.54/0.55  fof(f1078,plain,(
% 1.54/0.55    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~spl4_104),
% 1.54/0.55    inference(duplicate_literal_removal,[],[f1077])).
% 1.54/0.55  fof(f1077,plain,(
% 1.54/0.55    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~spl4_104),
% 1.54/0.55    inference(forward_demodulation,[],[f1076,f46])).
% 1.54/0.55  fof(f1076,plain,(
% 1.54/0.55    ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~spl4_104),
% 1.54/0.55    inference(forward_demodulation,[],[f1075,f46])).
% 1.54/0.55  fof(f1075,plain,(
% 1.54/0.55    ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~spl4_104),
% 1.54/0.55    inference(duplicate_literal_removal,[],[f1071])).
% 1.54/0.55  fof(f1071,plain,(
% 1.54/0.55    ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,sK2,k2_xboole_0(sK1,sK2))) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,sK2) | ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | ~spl4_104),
% 1.54/0.55    inference(resolution,[],[f1064,f56])).
% 1.54/0.55  fof(f56,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f36])).
% 1.54/0.55  fof(f1064,plain,(
% 1.54/0.55    ( ! [X0] : (~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,X0) | ~m1_subset_1(X0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2)))) ) | ~spl4_104),
% 1.54/0.55    inference(avatar_component_clause,[],[f1063])).
% 1.54/0.55  fof(f1065,plain,(
% 1.54/0.55    ~spl4_27 | spl4_104 | ~spl4_6 | ~spl4_102),
% 1.54/0.55    inference(avatar_split_clause,[],[f1057,f1050,f97,f1063,f313])).
% 1.54/0.55  fof(f1050,plain,(
% 1.54/0.55    spl4_102 <=> ! [X1,X0] : (~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).
% 1.54/0.55  fof(f1057,plain,(
% 1.54/0.55    ( ! [X0] : (~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),sK1,X0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(X0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK1,X0) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))) ) | (~spl4_6 | ~spl4_102)),
% 1.54/0.55    inference(resolution,[],[f1051,f98])).
% 1.54/0.55  fof(f98,plain,(
% 1.54/0.55    m1_subset_1(sK1,sK0) | ~spl4_6),
% 1.54/0.55    inference(avatar_component_clause,[],[f97])).
% 1.54/0.55  fof(f1051,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(X1,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))) ) | ~spl4_102),
% 1.54/0.55    inference(avatar_component_clause,[],[f1050])).
% 1.54/0.55  fof(f1052,plain,(
% 1.54/0.55    ~spl4_20 | spl4_102 | ~spl4_101),
% 1.54/0.55    inference(avatar_split_clause,[],[f1048,f1040,f1050,f268])).
% 1.54/0.55  fof(f1040,plain,(
% 1.54/0.55    spl4_101 <=> ! [X3,X2] : (~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X3,sK0) | ~m1_subset_1(X2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).
% 1.54/0.55  fof(f1048,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0)) ) | ~spl4_101),
% 1.54/0.55    inference(duplicate_literal_removal,[],[f1044])).
% 1.54/0.55  fof(f1044,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl4_101),
% 1.54/0.55    inference(resolution,[],[f1041,f133])).
% 1.54/0.55  fof(f133,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(k2_yellow_1(X0),X1,X2,X3),X0) | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3 | ~r1_orders_2(k2_yellow_1(X0),X2,X3) | ~r1_orders_2(k2_yellow_1(X0),X1,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 1.54/0.55    inference(global_subsumption,[],[f44,f45,f132])).
% 1.54/0.55  fof(f132,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(k2_yellow_1(X0),X1,X2,X3),X0) | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3 | ~r1_orders_2(k2_yellow_1(X0),X2,X3) | ~r1_orders_2(k2_yellow_1(X0),X1,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 1.54/0.55    inference(superposition,[],[f54,f46])).
% 1.54/0.55  fof(f54,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f36])).
% 1.54/0.55  fof(f45,plain,(
% 1.54/0.55    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.54/0.55    inference(cnf_transformation,[],[f16])).
% 1.54/0.55  fof(f16,plain,(
% 1.54/0.55    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 1.54/0.55    inference(pure_predicate_removal,[],[f7])).
% 1.54/0.55  fof(f7,axiom,(
% 1.54/0.55    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 1.54/0.55  fof(f44,plain,(
% 1.54/0.55    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 1.54/0.55    inference(cnf_transformation,[],[f17])).
% 1.54/0.55  fof(f17,plain,(
% 1.54/0.55    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 1.54/0.55    inference(pure_predicate_removal,[],[f15])).
% 1.54/0.55  fof(f15,plain,(
% 1.54/0.55    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.54/0.55    inference(pure_predicate_removal,[],[f8])).
% 1.54/0.55  fof(f8,axiom,(
% 1.54/0.55    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 1.54/0.55  fof(f1041,plain,(
% 1.54/0.55    ( ! [X2,X3] : (~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X3,sK0) | ~m1_subset_1(X2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)))) ) | ~spl4_101),
% 1.54/0.55    inference(avatar_component_clause,[],[f1040])).
% 1.54/0.55  fof(f1042,plain,(
% 1.54/0.55    spl4_11 | ~spl4_12 | ~spl4_13 | spl4_101 | ~spl4_6 | ~spl4_99),
% 1.54/0.55    inference(avatar_split_clause,[],[f1038,f1025,f97,f1040,f203,f200,f197])).
% 1.54/0.55  fof(f197,plain,(
% 1.54/0.55    spl4_11 <=> v2_struct_0(k2_yellow_1(sK0))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.54/0.55  fof(f200,plain,(
% 1.54/0.55    spl4_12 <=> v3_orders_2(k2_yellow_1(sK0))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.54/0.55  fof(f1025,plain,(
% 1.54/0.55    spl4_99 <=> ! [X3,X2] : (~m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(X3,sK0) | ~m1_subset_1(X2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).
% 1.54/0.55  fof(f1038,plain,(
% 1.54/0.55    ( ! [X2,X3] : (~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_99),
% 1.54/0.55    inference(forward_demodulation,[],[f1037,f46])).
% 1.54/0.55  fof(f1037,plain,(
% 1.54/0.55    ( ! [X2,X3] : (~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_99),
% 1.54/0.55    inference(duplicate_literal_removal,[],[f1036])).
% 1.54/0.55  fof(f1036,plain,(
% 1.54/0.55    ( ! [X2,X3] : (~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_99),
% 1.54/0.55    inference(forward_demodulation,[],[f1030,f46])).
% 1.54/0.55  fof(f1030,plain,(
% 1.54/0.55    ( ! [X2,X3] : (~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X2,X3) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | ~r1_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X3,k2_xboole_0(sK1,sK2)),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_99),
% 1.54/0.55    inference(resolution,[],[f1026,f66])).
% 1.54/0.55  fof(f66,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f37])).
% 1.54/0.55  fof(f37,plain,(
% 1.54/0.55    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.54/0.55    inference(nnf_transformation,[],[f27])).
% 1.54/0.55  fof(f27,plain,(
% 1.54/0.55    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.54/0.55    inference(flattening,[],[f26])).
% 1.54/0.55  fof(f26,plain,(
% 1.54/0.55    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.54/0.55    inference(ennf_transformation,[],[f5])).
% 1.54/0.55  fof(f5,axiom,(
% 1.54/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 1.54/0.55  fof(f1026,plain,(
% 1.54/0.55    ( ! [X2,X3] : (~r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(X3,sK0) | ~m1_subset_1(X2,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2))) ) | ~spl4_99),
% 1.54/0.55    inference(avatar_component_clause,[],[f1025])).
% 1.54/0.55  fof(f1027,plain,(
% 1.54/0.55    spl4_11 | ~spl4_12 | ~spl4_13 | spl4_99 | ~spl4_7 | ~spl4_97),
% 1.54/0.55    inference(avatar_split_clause,[],[f1023,f1011,f102,f1025,f203,f200,f197])).
% 1.54/0.55  fof(f1011,plain,(
% 1.54/0.55    spl4_97 <=> ! [X1,X0] : (~r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_97])])).
% 1.54/0.55  fof(f1023,plain,(
% 1.54/0.55    ( ! [X2,X3] : (~m1_subset_1(sK2,sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_97),
% 1.54/0.55    inference(forward_demodulation,[],[f1022,f46])).
% 1.54/0.55  fof(f1022,plain,(
% 1.54/0.55    ( ! [X2,X3] : (~m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_97),
% 1.54/0.55    inference(duplicate_literal_removal,[],[f1021])).
% 1.54/0.55  fof(f1021,plain,(
% 1.54/0.55    ( ! [X2,X3] : (~m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_97),
% 1.54/0.55    inference(forward_demodulation,[],[f1015,f46])).
% 1.54/0.55  fof(f1015,plain,(
% 1.54/0.55    ( ! [X2,X3] : (~r1_orders_2(k2_yellow_1(sK0),X2,k2_xboole_0(sK1,sK2)) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X3,X2) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X3,sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),sK0) | ~r1_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X3,X2,k2_xboole_0(sK1,sK2)),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) ) | ~spl4_97),
% 1.54/0.55    inference(resolution,[],[f1012,f66])).
% 1.54/0.55  fof(f1012,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0)) ) | ~spl4_97),
% 1.54/0.55    inference(avatar_component_clause,[],[f1011])).
% 1.54/0.55  fof(f1013,plain,(
% 1.54/0.55    ~spl4_6 | spl4_97 | spl4_5 | ~spl4_96),
% 1.54/0.55    inference(avatar_split_clause,[],[f1009,f1004,f88,f1011,f97])).
% 1.54/0.55  fof(f88,plain,(
% 1.54/0.55    spl4_5 <=> v1_xboole_0(sK0)),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.54/0.55  fof(f1004,plain,(
% 1.54/0.55    spl4_96 <=> ! [X1,X0] : (~m1_subset_1(X0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) | ~r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0) | ~r1_tarski(sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(X1,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 1.54/0.55  fof(f1009,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(sK1,sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))) ) | (spl4_5 | ~spl4_96)),
% 1.54/0.55    inference(duplicate_literal_removal,[],[f1008])).
% 1.54/0.55  fof(f1008,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0) | ~m1_subset_1(sK1,sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))) ) | (spl4_5 | ~spl4_96)),
% 1.54/0.55    inference(resolution,[],[f1007,f89])).
% 1.54/0.55  fof(f89,plain,(
% 1.54/0.55    ~v1_xboole_0(sK0) | spl4_5),
% 1.54/0.55    inference(avatar_component_clause,[],[f88])).
% 1.54/0.55  fof(f1007,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)),sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)),X2) | ~m1_subset_1(sK1,X2) | ~r3_orders_2(k2_yellow_1(X2),sK1,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))) ) | ~spl4_96),
% 1.54/0.55    inference(resolution,[],[f1005,f94])).
% 1.54/0.55  fof(f94,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | v1_xboole_0(X0)) )),
% 1.54/0.55    inference(forward_demodulation,[],[f93,f46])).
% 1.54/0.55  fof(f93,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.54/0.55    inference(forward_demodulation,[],[f49,f46])).
% 1.54/0.55  fof(f49,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f34])).
% 1.54/0.55  fof(f34,plain,(
% 1.54/0.55    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.54/0.55    inference(nnf_transformation,[],[f22])).
% 1.54/0.55  fof(f22,plain,(
% 1.54/0.55    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.54/0.55    inference(ennf_transformation,[],[f11])).
% 1.54/0.55  fof(f11,axiom,(
% 1.54/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 1.54/0.55  fof(f1005,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~r1_tarski(sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) | ~r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1)) ) | ~spl4_96),
% 1.54/0.55    inference(avatar_component_clause,[],[f1004])).
% 1.54/0.55  fof(f1006,plain,(
% 1.54/0.55    ~spl4_7 | spl4_96 | ~spl4_2 | spl4_5 | ~spl4_73),
% 1.54/0.55    inference(avatar_split_clause,[],[f1002,f726,f88,f76,f1004,f102])).
% 1.54/0.55  fof(f76,plain,(
% 1.54/0.55    spl4_2 <=> r2_hidden(k2_xboole_0(sK1,sK2),sK0)),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.54/0.55  fof(f726,plain,(
% 1.54/0.55    spl4_73 <=> ! [X1,X0,X2] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~r1_tarski(X1,sK3(k2_yellow_1(sK0),X2,X0,X1)) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X0,X1),sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X2,sK0) | k10_lattice3(k2_yellow_1(sK0),X2,X0) = X1 | ~r1_orders_2(k2_yellow_1(sK0),X2,X1))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 1.54/0.55  fof(f1002,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X1,sK0) | ~r1_tarski(sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0) | ~m1_subset_1(sK2,sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))) ) | (~spl4_2 | spl4_5 | ~spl4_73)),
% 1.54/0.55    inference(duplicate_literal_removal,[],[f1001])).
% 1.54/0.55  fof(f1001,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X1,sK0) | ~r1_tarski(sK1,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2)),sK0) | ~m1_subset_1(sK2,sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2))) ) | (~spl4_2 | spl4_5 | ~spl4_73)),
% 1.54/0.55    inference(resolution,[],[f954,f89])).
% 1.54/0.55  fof(f954,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X1,sK0) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X1,X0) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X0,sK0) | ~r1_tarski(sK1,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)),sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)),X2) | ~m1_subset_1(sK2,X2) | ~r3_orders_2(k2_yellow_1(X2),sK2,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2))) ) | (~spl4_2 | ~spl4_73)),
% 1.54/0.55    inference(resolution,[],[f951,f94])).
% 1.54/0.55  fof(f951,plain,(
% 1.54/0.55    ( ! [X0,X1] : (~r1_tarski(sK2,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2))) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X1,sK0) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),X1,X0) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(X0,sK0) | ~r1_tarski(sK1,sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X1,X0,k2_xboole_0(sK1,sK2)),sK0)) ) | (~spl4_2 | ~spl4_73)),
% 1.54/0.55    inference(resolution,[],[f948,f77])).
% 1.54/0.55  fof(f77,plain,(
% 1.54/0.55    r2_hidden(k2_xboole_0(sK1,sK2),sK0) | ~spl4_2),
% 1.54/0.55    inference(avatar_component_clause,[],[f76])).
% 1.54/0.55  fof(f948,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_xboole_0(X2,X3),sK0) | ~m1_subset_1(X1,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X1,k2_xboole_0(X2,X3)) | ~m1_subset_1(X0,sK0) | k2_xboole_0(X2,X3) = k10_lattice3(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(X2,X3)) | ~r1_tarski(X3,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(X2,X3))) | ~r1_tarski(X2,sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(X2,X3))) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X0,X1,k2_xboole_0(X2,X3)),sK0)) ) | ~spl4_73),
% 1.54/0.55    inference(resolution,[],[f807,f64])).
% 1.54/0.55  fof(f64,plain,(
% 1.54/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f25])).
% 1.54/0.55  fof(f25,plain,(
% 1.54/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.54/0.55    inference(ennf_transformation,[],[f4])).
% 1.54/0.55  fof(f4,axiom,(
% 1.54/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.54/0.55  fof(f807,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_xboole_0(X1,X2),sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X3,X0,k2_xboole_0(X1,X2)),sK0) | ~m1_subset_1(X0,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X0,k2_xboole_0(X1,X2)) | ~m1_subset_1(X3,sK0) | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(sK0),X3,X0) | ~r1_orders_2(k2_yellow_1(sK0),X3,k2_xboole_0(X1,X2)) | ~r1_tarski(X2,sK3(k2_yellow_1(sK0),X3,X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X1,sK3(k2_yellow_1(sK0),X3,X0,k2_xboole_0(X1,X2)))) ) | ~spl4_73),
% 1.54/0.55    inference(resolution,[],[f727,f67])).
% 1.54/0.55  fof(f67,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f29])).
% 1.54/0.55  fof(f29,plain,(
% 1.54/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.54/0.55    inference(flattening,[],[f28])).
% 1.54/0.55  fof(f28,plain,(
% 1.54/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.54/0.55    inference(ennf_transformation,[],[f3])).
% 1.54/0.55  fof(f3,axiom,(
% 1.54/0.55    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.54/0.55  fof(f727,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK3(k2_yellow_1(sK0),X2,X0,X1)) | ~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X0,X1),sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X2,sK0) | k10_lattice3(k2_yellow_1(sK0),X2,X0) = X1 | ~r1_orders_2(k2_yellow_1(sK0),X2,X1)) ) | ~spl4_73),
% 1.54/0.55    inference(avatar_component_clause,[],[f726])).
% 1.54/0.55  fof(f728,plain,(
% 1.54/0.55    spl4_5 | spl4_73 | spl4_5),
% 1.54/0.55    inference(avatar_split_clause,[],[f724,f88,f726,f88])).
% 1.54/0.55  fof(f724,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X2,X1) | k10_lattice3(k2_yellow_1(sK0),X2,X0) = X1 | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X0,X1),sK0) | ~r1_tarski(X1,sK3(k2_yellow_1(sK0),X2,X0,X1)) | v1_xboole_0(sK0)) ) | spl4_5),
% 1.54/0.55    inference(duplicate_literal_removal,[],[f722])).
% 1.54/0.55  fof(f722,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~r1_orders_2(k2_yellow_1(sK0),X2,X1) | k10_lattice3(k2_yellow_1(sK0),X2,X0) = X1 | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK3(k2_yellow_1(sK0),X2,X0,X1),sK0) | ~m1_subset_1(X1,sK0) | ~r1_tarski(X1,sK3(k2_yellow_1(sK0),X2,X0,X1)) | v1_xboole_0(sK0)) ) | spl4_5),
% 1.54/0.55    inference(resolution,[],[f569,f92])).
% 1.54/0.55  fof(f92,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 1.54/0.55    inference(forward_demodulation,[],[f91,f46])).
% 1.54/0.55  fof(f91,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.54/0.55    inference(forward_demodulation,[],[f50,f46])).
% 1.54/0.55  fof(f50,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f34])).
% 1.54/0.55  fof(f569,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(sK0),X2,sK3(k2_yellow_1(sK0),X0,X1,X2)) | ~r1_orders_2(k2_yellow_1(sK0),X1,X2) | ~r1_orders_2(k2_yellow_1(sK0),X0,X2) | k10_lattice3(k2_yellow_1(sK0),X0,X1) = X2 | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X2,sK0) | ~m1_subset_1(X1,sK0)) ) | spl4_5),
% 1.54/0.55    inference(resolution,[],[f413,f89])).
% 1.54/0.55  fof(f413,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~r1_orders_2(k2_yellow_1(X0),X2,X3) | ~r1_orders_2(k2_yellow_1(X0),X1,X3) | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3 | ~r3_orders_2(k2_yellow_1(X0),X3,sK3(k2_yellow_1(X0),X1,X2,X3)) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0)) )),
% 1.54/0.55    inference(global_subsumption,[],[f44,f45,f132,f412])).
% 1.54/0.55  fof(f412,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3(k2_yellow_1(X0),X1,X2,X3),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_orders_2(k2_yellow_1(X0),X2,X3) | ~r1_orders_2(k2_yellow_1(X0),X1,X3) | k10_lattice3(k2_yellow_1(X0),X1,X2) = X3 | ~r3_orders_2(k2_yellow_1(X0),X3,sK3(k2_yellow_1(X0),X1,X2,X3)) | ~m1_subset_1(X3,X0) | v1_xboole_0(X0)) )),
% 1.54/0.55    inference(resolution,[],[f161,f48])).
% 1.54/0.55  fof(f48,plain,(
% 1.54/0.55    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f21])).
% 1.54/0.55  fof(f21,plain,(
% 1.54/0.55    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 1.54/0.55    inference(ennf_transformation,[],[f18])).
% 1.54/0.55  fof(f18,plain,(
% 1.54/0.55    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 1.54/0.55    inference(pure_predicate_removal,[],[f9])).
% 1.54/0.55  fof(f9,axiom,(
% 1.54/0.55    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 1.54/0.55  fof(f161,plain,(
% 1.54/0.55    ( ! [X14,X12,X15,X13] : (v2_struct_0(k2_yellow_1(X13)) | ~m1_subset_1(sK3(k2_yellow_1(X13),X15,X12,X14),X13) | ~m1_subset_1(X12,X13) | ~m1_subset_1(X15,X13) | ~r1_orders_2(k2_yellow_1(X13),X12,X14) | ~r1_orders_2(k2_yellow_1(X13),X15,X14) | k10_lattice3(k2_yellow_1(X13),X15,X12) = X14 | ~r3_orders_2(k2_yellow_1(X13),X14,sK3(k2_yellow_1(X13),X15,X12,X14)) | ~m1_subset_1(X14,X13)) )),
% 1.54/0.55    inference(global_subsumption,[],[f43,f45,f160])).
% 1.54/0.55  fof(f160,plain,(
% 1.54/0.55    ( ! [X14,X12,X15,X13] : (~m1_subset_1(X14,X13) | ~m1_subset_1(sK3(k2_yellow_1(X13),X15,X12,X14),X13) | ~m1_subset_1(X12,X13) | ~m1_subset_1(X15,X13) | ~r1_orders_2(k2_yellow_1(X13),X12,X14) | ~r1_orders_2(k2_yellow_1(X13),X15,X14) | k10_lattice3(k2_yellow_1(X13),X15,X12) = X14 | ~r3_orders_2(k2_yellow_1(X13),X14,sK3(k2_yellow_1(X13),X15,X12,X14)) | ~l1_orders_2(k2_yellow_1(X13)) | ~v3_orders_2(k2_yellow_1(X13)) | v2_struct_0(k2_yellow_1(X13))) )),
% 1.54/0.55    inference(duplicate_literal_removal,[],[f159])).
% 1.54/0.55  fof(f159,plain,(
% 1.54/0.55    ( ! [X14,X12,X15,X13] : (~m1_subset_1(X14,X13) | ~m1_subset_1(sK3(k2_yellow_1(X13),X15,X12,X14),X13) | ~m1_subset_1(X12,X13) | ~m1_subset_1(X14,X13) | ~m1_subset_1(X15,X13) | ~r1_orders_2(k2_yellow_1(X13),X12,X14) | ~r1_orders_2(k2_yellow_1(X13),X15,X14) | k10_lattice3(k2_yellow_1(X13),X15,X12) = X14 | ~r3_orders_2(k2_yellow_1(X13),X14,sK3(k2_yellow_1(X13),X15,X12,X14)) | ~l1_orders_2(k2_yellow_1(X13)) | ~v3_orders_2(k2_yellow_1(X13)) | v2_struct_0(k2_yellow_1(X13))) )),
% 1.54/0.55    inference(forward_demodulation,[],[f158,f46])).
% 1.54/0.55  fof(f158,plain,(
% 1.54/0.55    ( ! [X14,X12,X15,X13] : (~m1_subset_1(sK3(k2_yellow_1(X13),X15,X12,X14),X13) | ~m1_subset_1(X12,X13) | ~m1_subset_1(X14,X13) | ~m1_subset_1(X15,X13) | ~r1_orders_2(k2_yellow_1(X13),X12,X14) | ~r1_orders_2(k2_yellow_1(X13),X15,X14) | k10_lattice3(k2_yellow_1(X13),X15,X12) = X14 | ~r3_orders_2(k2_yellow_1(X13),X14,sK3(k2_yellow_1(X13),X15,X12,X14)) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(X13))) | ~l1_orders_2(k2_yellow_1(X13)) | ~v3_orders_2(k2_yellow_1(X13)) | v2_struct_0(k2_yellow_1(X13))) )),
% 1.54/0.55    inference(forward_demodulation,[],[f143,f46])).
% 1.54/0.55  fof(f143,plain,(
% 1.54/0.55    ( ! [X14,X12,X15,X13] : (~m1_subset_1(X12,X13) | ~m1_subset_1(X14,X13) | ~m1_subset_1(X15,X13) | ~r1_orders_2(k2_yellow_1(X13),X12,X14) | ~r1_orders_2(k2_yellow_1(X13),X15,X14) | k10_lattice3(k2_yellow_1(X13),X15,X12) = X14 | ~r3_orders_2(k2_yellow_1(X13),X14,sK3(k2_yellow_1(X13),X15,X12,X14)) | ~m1_subset_1(sK3(k2_yellow_1(X13),X15,X12,X14),u1_struct_0(k2_yellow_1(X13))) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(X13))) | ~l1_orders_2(k2_yellow_1(X13)) | ~v3_orders_2(k2_yellow_1(X13)) | v2_struct_0(k2_yellow_1(X13))) )),
% 1.54/0.55    inference(resolution,[],[f138,f65])).
% 1.54/0.55  fof(f65,plain,(
% 1.54/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f37])).
% 1.54/0.55  fof(f138,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,sK3(k2_yellow_1(X0),X2,X3,X1)) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~r1_orders_2(k2_yellow_1(X0),X3,X1) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | k10_lattice3(k2_yellow_1(X0),X2,X3) = X1) )),
% 1.54/0.55    inference(global_subsumption,[],[f45,f137])).
% 1.54/0.55  fof(f137,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X1,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,sK3(k2_yellow_1(X0),X2,X3,X1)) | ~r1_orders_2(k2_yellow_1(X0),X3,X1) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | ~l1_orders_2(k2_yellow_1(X0)) | k10_lattice3(k2_yellow_1(X0),X2,X3) = X1) )),
% 1.54/0.55    inference(forward_demodulation,[],[f136,f46])).
% 1.54/0.55  fof(f136,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,X0) | ~m1_subset_1(X1,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,sK3(k2_yellow_1(X0),X2,X3,X1)) | ~r1_orders_2(k2_yellow_1(X0),X3,X1) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | k10_lattice3(k2_yellow_1(X0),X2,X3) = X1) )),
% 1.54/0.55    inference(forward_demodulation,[],[f135,f46])).
% 1.54/0.55  fof(f135,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,sK3(k2_yellow_1(X0),X2,X3,X1)) | ~r1_orders_2(k2_yellow_1(X0),X3,X1) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | k10_lattice3(k2_yellow_1(X0),X2,X3) = X1) )),
% 1.54/0.55    inference(forward_demodulation,[],[f134,f46])).
% 1.54/0.55  fof(f134,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,sK3(k2_yellow_1(X0),X2,X3,X1)) | ~r1_orders_2(k2_yellow_1(X0),X3,X1) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | k10_lattice3(k2_yellow_1(X0),X2,X3) = X1) )),
% 1.54/0.55    inference(resolution,[],[f57,f44])).
% 1.54/0.55  fof(f57,plain,(
% 1.54/0.55    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k10_lattice3(X0,X1,X2) = X3) )),
% 1.54/0.55    inference(cnf_transformation,[],[f36])).
% 1.54/0.55  fof(f43,plain,(
% 1.54/0.55    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 1.54/0.55    inference(cnf_transformation,[],[f17])).
% 1.54/0.55  fof(f719,plain,(
% 1.54/0.55    spl4_5 | ~spl4_18 | ~spl4_7 | ~spl4_20 | spl4_72),
% 1.54/0.55    inference(avatar_split_clause,[],[f717,f714,f268,f102,f249,f88])).
% 1.54/0.55  fof(f249,plain,(
% 1.54/0.55    spl4_18 <=> r1_tarski(sK2,k2_xboole_0(sK1,sK2))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.54/0.55  fof(f714,plain,(
% 1.54/0.55    spl4_72 <=> r3_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 1.54/0.55  fof(f717,plain,(
% 1.54/0.55    ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,sK0) | ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | v1_xboole_0(sK0) | spl4_72),
% 1.54/0.55    inference(resolution,[],[f715,f92])).
% 1.54/0.55  fof(f715,plain,(
% 1.54/0.55    ~r3_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | spl4_72),
% 1.54/0.55    inference(avatar_component_clause,[],[f714])).
% 1.54/0.55  fof(f716,plain,(
% 1.54/0.55    spl4_11 | ~spl4_12 | ~spl4_13 | ~spl4_72 | ~spl4_20 | ~spl4_7 | spl4_35),
% 1.54/0.55    inference(avatar_split_clause,[],[f712,f363,f102,f268,f714,f203,f200,f197])).
% 1.54/0.55  fof(f712,plain,(
% 1.54/0.55    ~m1_subset_1(sK2,sK0) | ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_35),
% 1.54/0.55    inference(forward_demodulation,[],[f711,f46])).
% 1.54/0.55  fof(f711,plain,(
% 1.54/0.55    ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_35),
% 1.54/0.55    inference(forward_demodulation,[],[f710,f46])).
% 1.54/0.55  fof(f710,plain,(
% 1.54/0.55    ~r3_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_35),
% 1.54/0.55    inference(resolution,[],[f685,f65])).
% 1.54/0.55  fof(f685,plain,(
% 1.54/0.55    ~r1_orders_2(k2_yellow_1(sK0),sK2,k2_xboole_0(sK1,sK2)) | spl4_35),
% 1.54/0.55    inference(avatar_component_clause,[],[f363])).
% 1.54/0.55  fof(f663,plain,(
% 1.54/0.55    spl4_5 | ~spl4_17 | ~spl4_6 | ~spl4_20 | spl4_66),
% 1.54/0.55    inference(avatar_split_clause,[],[f661,f635,f268,f97,f246,f88])).
% 1.54/0.55  fof(f246,plain,(
% 1.54/0.55    spl4_17 <=> r1_tarski(sK1,k2_xboole_0(sK1,sK2))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.54/0.55  fof(f635,plain,(
% 1.54/0.55    spl4_66 <=> r3_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 1.54/0.55  fof(f661,plain,(
% 1.54/0.55    ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK1,sK0) | ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | v1_xboole_0(sK0) | spl4_66),
% 1.54/0.55    inference(resolution,[],[f636,f92])).
% 1.54/0.55  fof(f636,plain,(
% 1.54/0.55    ~r3_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | spl4_66),
% 1.54/0.55    inference(avatar_component_clause,[],[f635])).
% 1.54/0.55  fof(f637,plain,(
% 1.54/0.55    spl4_11 | ~spl4_12 | ~spl4_13 | ~spl4_66 | ~spl4_20 | ~spl4_6 | spl4_27),
% 1.54/0.55    inference(avatar_split_clause,[],[f633,f313,f97,f268,f635,f203,f200,f197])).
% 1.54/0.55  fof(f633,plain,(
% 1.54/0.55    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_27),
% 1.54/0.55    inference(forward_demodulation,[],[f632,f46])).
% 1.54/0.55  fof(f632,plain,(
% 1.54/0.55    ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | ~r3_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_27),
% 1.54/0.55    inference(forward_demodulation,[],[f631,f46])).
% 1.54/0.55  fof(f631,plain,(
% 1.54/0.55    ~r3_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | spl4_27),
% 1.54/0.55    inference(resolution,[],[f606,f65])).
% 1.54/0.55  fof(f606,plain,(
% 1.54/0.55    ~r1_orders_2(k2_yellow_1(sK0),sK1,k2_xboole_0(sK1,sK2)) | spl4_27),
% 1.54/0.55    inference(avatar_component_clause,[],[f313])).
% 1.54/0.55  fof(f518,plain,(
% 1.54/0.55    spl4_51),
% 1.54/0.55    inference(avatar_contradiction_clause,[],[f517])).
% 1.54/0.55  fof(f517,plain,(
% 1.54/0.55    $false | spl4_51),
% 1.54/0.55    inference(resolution,[],[f501,f44])).
% 1.54/0.55  fof(f501,plain,(
% 1.54/0.55    ~v5_orders_2(k2_yellow_1(sK0)) | spl4_51),
% 1.54/0.55    inference(avatar_component_clause,[],[f500])).
% 1.54/0.55  fof(f278,plain,(
% 1.54/0.55    spl4_5 | ~spl4_11),
% 1.54/0.55    inference(avatar_split_clause,[],[f277,f197,f88])).
% 1.54/0.55  fof(f277,plain,(
% 1.54/0.55    v1_xboole_0(sK0) | ~spl4_11),
% 1.54/0.55    inference(resolution,[],[f198,f48])).
% 1.54/0.55  fof(f198,plain,(
% 1.54/0.55    v2_struct_0(k2_yellow_1(sK0)) | ~spl4_11),
% 1.54/0.55    inference(avatar_component_clause,[],[f197])).
% 1.54/0.55  fof(f276,plain,(
% 1.54/0.55    ~spl4_2 | spl4_20),
% 1.54/0.55    inference(avatar_split_clause,[],[f274,f268,f76])).
% 1.54/0.55  fof(f274,plain,(
% 1.54/0.55    ~r2_hidden(k2_xboole_0(sK1,sK2),sK0) | spl4_20),
% 1.54/0.55    inference(resolution,[],[f269,f64])).
% 1.54/0.55  fof(f269,plain,(
% 1.54/0.55    ~m1_subset_1(k2_xboole_0(sK1,sK2),sK0) | spl4_20),
% 1.54/0.55    inference(avatar_component_clause,[],[f268])).
% 1.54/0.55  fof(f260,plain,(
% 1.54/0.55    spl4_18),
% 1.54/0.55    inference(avatar_contradiction_clause,[],[f258])).
% 1.54/0.55  fof(f258,plain,(
% 1.54/0.55    $false | spl4_18),
% 1.54/0.55    inference(resolution,[],[f250,f105])).
% 1.54/0.55  fof(f105,plain,(
% 1.54/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.54/0.55    inference(superposition,[],[f62,f63])).
% 1.54/0.55  fof(f63,plain,(
% 1.54/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.54/0.55    inference(cnf_transformation,[],[f1])).
% 1.54/0.55  fof(f1,axiom,(
% 1.54/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.54/0.55  fof(f62,plain,(
% 1.54/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.54/0.55    inference(cnf_transformation,[],[f2])).
% 1.54/0.55  fof(f2,axiom,(
% 1.54/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.54/0.55  fof(f250,plain,(
% 1.54/0.55    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | spl4_18),
% 1.54/0.55    inference(avatar_component_clause,[],[f249])).
% 1.54/0.55  fof(f257,plain,(
% 1.54/0.55    spl4_17),
% 1.54/0.55    inference(avatar_contradiction_clause,[],[f255])).
% 1.54/0.55  fof(f255,plain,(
% 1.54/0.55    $false | spl4_17),
% 1.54/0.55    inference(resolution,[],[f247,f62])).
% 1.54/0.55  fof(f247,plain,(
% 1.54/0.55    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | spl4_17),
% 1.54/0.55    inference(avatar_component_clause,[],[f246])).
% 1.54/0.55  fof(f212,plain,(
% 1.54/0.55    spl4_13),
% 1.54/0.55    inference(avatar_contradiction_clause,[],[f211])).
% 1.54/0.55  fof(f211,plain,(
% 1.54/0.55    $false | spl4_13),
% 1.54/0.55    inference(resolution,[],[f204,f45])).
% 1.54/0.55  fof(f204,plain,(
% 1.54/0.55    ~l1_orders_2(k2_yellow_1(sK0)) | spl4_13),
% 1.54/0.55    inference(avatar_component_clause,[],[f203])).
% 1.54/0.55  fof(f210,plain,(
% 1.54/0.55    spl4_12),
% 1.54/0.55    inference(avatar_contradiction_clause,[],[f209])).
% 1.54/0.55  fof(f209,plain,(
% 1.54/0.55    $false | spl4_12),
% 1.54/0.55    inference(resolution,[],[f201,f43])).
% 1.54/0.55  fof(f201,plain,(
% 1.54/0.55    ~v3_orders_2(k2_yellow_1(sK0)) | spl4_12),
% 1.54/0.55    inference(avatar_component_clause,[],[f200])).
% 1.54/0.55  fof(f104,plain,(
% 1.54/0.55    spl4_7 | ~spl4_3),
% 1.54/0.55    inference(avatar_split_clause,[],[f100,f80,f102])).
% 1.54/0.55  fof(f80,plain,(
% 1.54/0.55    spl4_3 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.54/0.55  fof(f100,plain,(
% 1.54/0.55    m1_subset_1(sK2,sK0) | ~spl4_3),
% 1.54/0.55    inference(forward_demodulation,[],[f81,f46])).
% 1.54/0.55  fof(f81,plain,(
% 1.54/0.55    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_3),
% 1.54/0.55    inference(avatar_component_clause,[],[f80])).
% 1.54/0.55  fof(f99,plain,(
% 1.54/0.55    spl4_6 | ~spl4_4),
% 1.54/0.55    inference(avatar_split_clause,[],[f95,f84,f97])).
% 1.54/0.55  fof(f84,plain,(
% 1.54/0.55    spl4_4 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 1.54/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.54/0.55  fof(f95,plain,(
% 1.54/0.55    m1_subset_1(sK1,sK0) | ~spl4_4),
% 1.54/0.55    inference(forward_demodulation,[],[f85,f46])).
% 1.54/0.55  fof(f85,plain,(
% 1.54/0.55    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_4),
% 1.54/0.55    inference(avatar_component_clause,[],[f84])).
% 1.54/0.55  fof(f90,plain,(
% 1.54/0.55    ~spl4_5),
% 1.54/0.55    inference(avatar_split_clause,[],[f38,f88])).
% 1.54/0.55  fof(f38,plain,(
% 1.54/0.55    ~v1_xboole_0(sK0)),
% 1.54/0.55    inference(cnf_transformation,[],[f33])).
% 1.54/0.55  fof(f33,plain,(
% 1.54/0.55    ((k2_xboole_0(sK1,sK2) != k10_lattice3(k2_yellow_1(sK0),sK1,sK2) & r2_hidden(k2_xboole_0(sK1,sK2),sK0) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & ~v1_xboole_0(sK0)),
% 1.54/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f32,f31,f30])).
% 1.54/0.55  fof(f30,plain,(
% 1.54/0.55    ? [X0] : (? [X1] : (? [X2] : (k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),X0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(sK0),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),sK0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & ~v1_xboole_0(sK0))),
% 1.54/0.55    introduced(choice_axiom,[])).
% 1.54/0.55  fof(f31,plain,(
% 1.54/0.55    ? [X1] : (? [X2] : (k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(sK0),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),sK0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (k2_xboole_0(sK1,X2) != k10_lattice3(k2_yellow_1(sK0),sK1,X2) & r2_hidden(k2_xboole_0(sK1,X2),sK0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 1.54/0.55    introduced(choice_axiom,[])).
% 1.54/0.55  fof(f32,plain,(
% 1.54/0.55    ? [X2] : (k2_xboole_0(sK1,X2) != k10_lattice3(k2_yellow_1(sK0),sK1,X2) & r2_hidden(k2_xboole_0(sK1,X2),sK0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (k2_xboole_0(sK1,sK2) != k10_lattice3(k2_yellow_1(sK0),sK1,sK2) & r2_hidden(k2_xboole_0(sK1,sK2),sK0) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 1.54/0.55    introduced(choice_axiom,[])).
% 1.54/0.55  fof(f20,plain,(
% 1.54/0.55    ? [X0] : (? [X1] : (? [X2] : (k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),X0) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 1.54/0.55    inference(flattening,[],[f19])).
% 1.54/0.55  fof(f19,plain,(
% 1.54/0.55    ? [X0] : (? [X1] : (? [X2] : ((k2_xboole_0(X1,X2) != k10_lattice3(k2_yellow_1(X0),X1,X2) & r2_hidden(k2_xboole_0(X1,X2),X0)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 1.54/0.55    inference(ennf_transformation,[],[f13])).
% 1.54/0.55  fof(f13,negated_conjecture,(
% 1.54/0.55    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 1.54/0.55    inference(negated_conjecture,[],[f12])).
% 1.54/0.55  fof(f12,conjecture,(
% 1.54/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 1.54/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).
% 1.54/0.55  fof(f86,plain,(
% 1.54/0.55    spl4_4),
% 1.54/0.55    inference(avatar_split_clause,[],[f39,f84])).
% 1.54/0.55  fof(f39,plain,(
% 1.54/0.55    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 1.54/0.55    inference(cnf_transformation,[],[f33])).
% 1.54/0.55  fof(f82,plain,(
% 1.54/0.55    spl4_3),
% 1.54/0.55    inference(avatar_split_clause,[],[f40,f80])).
% 1.54/0.55  fof(f40,plain,(
% 1.54/0.55    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 1.54/0.55    inference(cnf_transformation,[],[f33])).
% 1.54/0.55  fof(f78,plain,(
% 1.54/0.55    spl4_2),
% 1.54/0.55    inference(avatar_split_clause,[],[f41,f76])).
% 1.54/0.55  fof(f41,plain,(
% 1.54/0.55    r2_hidden(k2_xboole_0(sK1,sK2),sK0)),
% 1.54/0.55    inference(cnf_transformation,[],[f33])).
% 1.54/0.55  fof(f74,plain,(
% 1.54/0.55    ~spl4_1),
% 1.54/0.55    inference(avatar_split_clause,[],[f42,f72])).
% 1.54/0.55  fof(f42,plain,(
% 1.54/0.55    k2_xboole_0(sK1,sK2) != k10_lattice3(k2_yellow_1(sK0),sK1,sK2)),
% 1.54/0.55    inference(cnf_transformation,[],[f33])).
% 1.54/0.55  % SZS output end Proof for theBenchmark
% 1.54/0.55  % (11675)------------------------------
% 1.54/0.55  % (11675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.55  % (11675)Termination reason: Refutation
% 1.54/0.55  
% 1.54/0.55  % (11675)Memory used [KB]: 11513
% 1.54/0.55  % (11675)Time elapsed: 0.140 s
% 1.54/0.55  % (11675)------------------------------
% 1.54/0.55  % (11675)------------------------------
% 1.54/0.55  % (11665)Success in time 0.194 s
%------------------------------------------------------------------------------
