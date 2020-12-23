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
% DateTime   : Thu Dec  3 13:16:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 241 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   21
%              Number of atoms          :  621 (1036 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f109,f116,f118,f150,f173,f205,f234,f236])).

fof(f236,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_14
    | spl4_15 ),
    inference(avatar_split_clause,[],[f235,f232,f202,f80,f76])).

fof(f76,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f80,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f202,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( r1_tarski(k12_lattice3(k2_yellow_1(sK0),X1,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f232,plain,
    ( spl4_15
  <=> r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f235,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_14
    | spl4_15 ),
    inference(resolution,[],[f233,f203])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k12_lattice3(k2_yellow_1(sK0),X1,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f202])).

fof(f233,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f232])).

fof(f234,plain,
    ( ~ spl4_15
    | ~ spl4_3
    | ~ spl4_2
    | spl4_6
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f224,f171,f114,f107,f76,f80,f232])).

fof(f107,plain,
    ( spl4_6
  <=> r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f114,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f171,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f224,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)
    | spl4_6
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(resolution,[],[f196,f108])).

fof(f108,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f196,plain,
    ( ! [X4,X5,X3] :
        ( r1_tarski(k12_lattice3(k2_yellow_1(sK0),X3,X4),k3_xboole_0(X5,X4))
        | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),X3,X4),X5) )
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(resolution,[],[f194,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f194,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(resolution,[],[f172,f115])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f205,plain,
    ( ~ spl4_9
    | ~ spl4_4
    | ~ spl4_7
    | spl4_14
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f199,f171,f114,f202,f111,f84,f141])).

fof(f141,plain,
    ( spl4_9
  <=> v5_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f84,plain,
    ( spl4_4
  <=> v2_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f111,plain,
    ( spl4_7
  <=> l1_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f199,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k12_lattice3(k2_yellow_1(sK0),X3,X2),X3)
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v2_lattice3(k2_yellow_1(sK0))
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k12_lattice3(k2_yellow_1(sK0),X3,X2),X3)
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ v2_lattice3(k2_yellow_1(sK0))
        | ~ v5_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(superposition,[],[f194,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
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
     => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

fof(f173,plain,
    ( spl4_5
    | spl4_11
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f168,f114,f84,f171,f88])).

fof(f88,plain,
    ( spl4_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1)
        | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | v1_xboole_0(sK0) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | v1_xboole_0(sK0) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f162,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f162,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f139,f115])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X1,X0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X1,X0),X0)
        | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f133,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | r3_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f96,f85])).

fof(f85,plain,
    ( v2_lattice3(k2_yellow_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | r3_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) ) ),
    inference(global_subsumption,[],[f51,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | r3_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X1))
      | ~ l1_orders_2(k2_yellow_1(X1)) ) ),
    inference(resolution,[],[f92,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(global_subsumption,[],[f49,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f63,f51])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f49,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f51,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f133,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(resolution,[],[f127,f115])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X1,X0),X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f120,f85])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2) ) ),
    inference(global_subsumption,[],[f51,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2) ) ),
    inference(resolution,[],[f69,f50])).

fof(f50,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

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
    inference(flattening,[],[f38])).

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
    inference(nnf_transformation,[],[f22])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f150,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f142,f50])).

fof(f142,plain,
    ( ~ v5_orders_2(k2_yellow_1(sK0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f118,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f112,f51])).

fof(f112,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f116,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f103,f84,f114,f111])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_4 ),
    inference(superposition,[],[f66,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( k12_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f94,f85])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | k12_lattice3(k2_yellow_1(X1),X2,X0) = k11_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(global_subsumption,[],[f51,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v2_lattice3(k2_yellow_1(X1))
      | k12_lattice3(k2_yellow_1(X1),X2,X0) = k11_lattice3(k2_yellow_1(X1),X2,X0) ) ),
    inference(resolution,[],[f64,f50])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f109,plain,
    ( ~ spl4_3
    | ~ spl4_2
    | ~ spl4_6
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f84,f72,f107,f76,f80])).

fof(f72,plain,
    ( spl4_1
  <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f101,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f73,f100])).

fof(f73,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f90,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f44,f88])).

fof(f44,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v2_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f35,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f86,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    v2_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f47,f76])).

fof(f47,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f48,f72])).

fof(f48,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:41 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.21/0.44  % (5033)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.45  % (5033)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f237,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f109,f116,f118,f150,f173,f205,f234,f236])).
% 0.21/0.45  fof(f236,plain,(
% 0.21/0.45    ~spl4_2 | ~spl4_3 | ~spl4_14 | spl4_15),
% 0.21/0.45    inference(avatar_split_clause,[],[f235,f232,f202,f80,f76])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl4_2 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl4_3 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.45  fof(f202,plain,(
% 0.21/0.45    spl4_14 <=> ! [X1,X0] : (r1_tarski(k12_lattice3(k2_yellow_1(sK0),X1,X0),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.45  fof(f232,plain,(
% 0.21/0.45    spl4_15 <=> r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.45  fof(f235,plain,(
% 0.21/0.45    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | (~spl4_14 | spl4_15)),
% 0.21/0.45    inference(resolution,[],[f233,f203])).
% 0.21/0.45  fof(f203,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k12_lattice3(k2_yellow_1(sK0),X1,X0),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f202])).
% 0.21/0.45  fof(f233,plain,(
% 0.21/0.45    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | spl4_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f232])).
% 0.21/0.45  fof(f234,plain,(
% 0.21/0.45    ~spl4_15 | ~spl4_3 | ~spl4_2 | spl4_6 | ~spl4_8 | ~spl4_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f224,f171,f114,f107,f76,f80,f232])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    spl4_6 <=> r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    spl4_8 <=> ! [X1,X0] : (m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.45  fof(f171,plain,(
% 0.21/0.45    spl4_11 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.45  fof(f224,plain,(
% 0.21/0.45    ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),sK1) | (spl4_6 | ~spl4_8 | ~spl4_11)),
% 0.21/0.45    inference(resolution,[],[f196,f108])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) | spl4_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f107])).
% 0.21/0.45  fof(f196,plain,(
% 0.21/0.45    ( ! [X4,X5,X3] : (r1_tarski(k12_lattice3(k2_yellow_1(sK0),X3,X4),k3_xboole_0(X5,X4)) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),X3,X4),X5)) ) | (~spl4_8 | ~spl4_11)),
% 0.21/0.45    inference(resolution,[],[f194,f67])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.45  fof(f194,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_8 | ~spl4_11)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f189])).
% 0.21/0.45  fof(f189,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_8 | ~spl4_11)),
% 0.21/0.45    inference(resolution,[],[f172,f115])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f114])).
% 0.21/0.45  fof(f172,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f171])).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    ~spl4_9 | ~spl4_4 | ~spl4_7 | spl4_14 | ~spl4_8 | ~spl4_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f199,f171,f114,f202,f111,f84,f141])).
% 0.21/0.45  fof(f141,plain,(
% 0.21/0.45    spl4_9 <=> v5_orders_2(k2_yellow_1(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    spl4_4 <=> v2_lattice3(k2_yellow_1(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    spl4_7 <=> l1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.45  fof(f199,plain,(
% 0.21/0.45    ( ! [X2,X3] : (r1_tarski(k12_lattice3(k2_yellow_1(sK0),X3,X2),X3) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))) ) | (~spl4_8 | ~spl4_11)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f198])).
% 0.21/0.45  fof(f198,plain,(
% 0.21/0.45    ( ! [X2,X3] : (r1_tarski(k12_lattice3(k2_yellow_1(sK0),X3,X2),X3) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v2_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))) ) | (~spl4_8 | ~spl4_11)),
% 0.21/0.45    inference(superposition,[],[f194,f65])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k12_lattice3)).
% 0.21/0.45  fof(f173,plain,(
% 0.21/0.45    spl4_5 | spl4_11 | ~spl4_4 | ~spl4_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f168,f114,f84,f171,f88])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    spl4_5 <=> v1_xboole_0(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.45  fof(f168,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0))) | v1_xboole_0(sK0)) ) | (~spl4_4 | ~spl4_8)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f163])).
% 0.21/0.45  fof(f163,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(k12_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0))) | v1_xboole_0(sK0)) ) | (~spl4_4 | ~spl4_8)),
% 0.21/0.45    inference(resolution,[],[f162,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.45  fof(f162,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_4 | ~spl4_8)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f157])).
% 0.21/0.45  fof(f157,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_4 | ~spl4_8)),
% 0.21/0.45    inference(resolution,[],[f139,f115])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X1,X0),X0) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_4 | ~spl4_8)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f134])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r3_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X1,X0),X0) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_4 | ~spl4_8)),
% 0.21/0.45    inference(resolution,[],[f133,f97])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_orders_2(k2_yellow_1(sK0),X0,X1) | r3_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_4),
% 0.21/0.45    inference(resolution,[],[f96,f85])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    v2_lattice3(k2_yellow_1(sK0)) | ~spl4_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f84])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | r3_orders_2(k2_yellow_1(X1),X2,X0) | ~r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))) )),
% 0.21/0.45    inference(global_subsumption,[],[f51,f95])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | r3_orders_2(k2_yellow_1(X1),X2,X0) | ~r1_orders_2(k2_yellow_1(X1),X2,X0) | ~v2_lattice3(k2_yellow_1(X1)) | ~l1_orders_2(k2_yellow_1(X1))) )),
% 0.21/0.45    inference(resolution,[],[f92,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.45    inference(global_subsumption,[],[f49,f91])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.45    inference(resolution,[],[f63,f51])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.21/0.45    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.45    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.45    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_4 | ~spl4_8)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f128])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_4 | ~spl4_8)),
% 0.21/0.45    inference(resolution,[],[f127,f115])).
% 0.21/0.45  fof(f127,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k12_lattice3(k2_yellow_1(sK0),X1,X0),X0)) ) | ~spl4_4),
% 0.21/0.45    inference(resolution,[],[f120,f85])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2)) )),
% 0.21/0.45    inference(global_subsumption,[],[f51,f119])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),k12_lattice3(k2_yellow_1(X0),X1,X2),X2)) )),
% 0.21/0.45    inference(resolution,[],[f69,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)) )),
% 0.21/0.45    inference(equality_resolution,[],[f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k12_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f42])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(rectify,[],[f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k12_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k12_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).
% 0.21/0.45  fof(f150,plain,(
% 0.21/0.45    spl4_9),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f149])).
% 0.21/0.45  fof(f149,plain,(
% 0.21/0.45    $false | spl4_9),
% 0.21/0.45    inference(resolution,[],[f142,f50])).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    ~v5_orders_2(k2_yellow_1(sK0)) | spl4_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f141])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    spl4_7),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f117])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    $false | spl4_7),
% 0.21/0.45    inference(resolution,[],[f112,f51])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    ~l1_orders_2(k2_yellow_1(sK0)) | spl4_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f111])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    ~spl4_7 | spl4_8 | ~spl4_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f103,f84,f114,f111])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))) ) | ~spl4_4),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(k12_lattice3(k2_yellow_1(sK0),X0,X1),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_4),
% 0.21/0.45    inference(superposition,[],[f66,f100])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k12_lattice3(k2_yellow_1(sK0),X0,X1) = k11_lattice3(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_4),
% 0.21/0.45    inference(resolution,[],[f94,f85])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v2_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | k12_lattice3(k2_yellow_1(X1),X2,X0) = k11_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.21/0.45    inference(global_subsumption,[],[f51,f93])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v2_lattice3(k2_yellow_1(X1)) | k12_lattice3(k2_yellow_1(X1),X2,X0) = k11_lattice3(k2_yellow_1(X1),X2,X0)) )),
% 0.21/0.45    inference(resolution,[],[f64,f50])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    ~spl4_3 | ~spl4_2 | ~spl4_6 | spl4_1 | ~spl4_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f101,f84,f72,f107,f76,f80])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl4_1 <=> r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ~r1_tarski(k12_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | (spl4_1 | ~spl4_4)),
% 0.21/0.45    inference(superposition,[],[f73,f100])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) | spl4_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f72])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    ~spl4_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f44,f88])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ~v1_xboole_0(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f35,f34,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v2_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,X2),k3_xboole_0(sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.21/0.45    inference(flattening,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f11])).
% 0.21/0.45  fof(f11,conjecture,(
% 0.21/0.45    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    spl4_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f45,f84])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    v2_lattice3(k2_yellow_1(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    spl4_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f46,f80])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl4_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f47,f76])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ~spl4_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f48,f72])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ~r1_tarski(k11_lattice3(k2_yellow_1(sK0),sK1,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (5033)------------------------------
% 0.21/0.45  % (5033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (5033)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (5033)Memory used [KB]: 10746
% 0.21/0.45  % (5033)Time elapsed: 0.042 s
% 0.21/0.45  % (5033)------------------------------
% 0.21/0.45  % (5033)------------------------------
% 0.21/0.46  % (5026)Success in time 0.097 s
%------------------------------------------------------------------------------
