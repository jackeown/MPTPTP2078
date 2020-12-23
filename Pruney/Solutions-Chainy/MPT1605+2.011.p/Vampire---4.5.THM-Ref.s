%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 173 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  434 ( 653 expanded)
%              Number of equality atoms :   44 (  94 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f100,f127,f130,f198,f204,f219])).

fof(f219,plain,
    ( ~ spl2_7
    | spl2_1
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f208,f202,f68,f115])).

fof(f115,plain,
    ( spl2_7
  <=> l1_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f68,plain,
    ( spl2_1
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f202,plain,
    ( spl2_20
  <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f208,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl2_20 ),
    inference(superposition,[],[f51,f203])).

fof(f203,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f51,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f204,plain,
    ( ~ spl2_7
    | spl2_20
    | ~ spl2_8
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f200,f196,f118,f202,f115])).

fof(f118,plain,
    ( spl2_8
  <=> m1_subset_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f196,plain,
    ( spl2_19
  <=> ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f200,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f199,f46])).

fof(f46,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f199,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl2_19 ),
    inference(resolution,[],[f197,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f197,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f196])).

fof(f198,plain,
    ( ~ spl2_8
    | spl2_19
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f193,f98,f196,f118])).

fof(f98,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0)
        | ~ m1_subset_1(k1_xboole_0,sK0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f192,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f192,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK1(k2_yellow_1(sK0),X0,X1))
        | ~ r2_lattice3(k2_yellow_1(sK0),X1,X0)
        | k1_yellow_0(k2_yellow_1(sK0),X1) = X0
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl2_4 ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ r2_lattice3(k2_yellow_1(sK0),X1,X0)
        | k1_yellow_0(k2_yellow_1(sK0),X1) = X0
        | ~ r2_lattice3(k2_yellow_1(sK0),X1,X0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(X0,sK1(k2_yellow_1(sK0),X0,X1))
        | k1_yellow_0(k2_yellow_1(sK0),X1) = X0
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f190,f162])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X2,sK1(k2_yellow_1(sK0),X1,X0))
        | ~ r2_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_tarski(X2,sK1(k2_yellow_1(sK0),X1,X0))
        | k1_yellow_0(k2_yellow_1(sK0),X0) = X1
        | ~ m1_subset_1(X2,sK0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f134,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,sK0)
        | ~ r1_tarski(X0,X1)
        | r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f44,f45,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f56,f46])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
        & r2_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f45,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f44,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2))
      | ~ m1_subset_1(X1,X0)
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(global_subsumption,[],[f45,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2))
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(forward_demodulation,[],[f188,f46])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2))
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(resolution,[],[f58,f44])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f130,plain,
    ( ~ spl2_2
    | spl2_8 ),
    inference(avatar_split_clause,[],[f128,f118,f72])).

fof(f72,plain,
    ( spl2_2
  <=> r2_hidden(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f128,plain,
    ( ~ r2_hidden(k1_xboole_0,sK0)
    | spl2_8 ),
    inference(resolution,[],[f119,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f119,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f127,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f116,f45])).

fof(f116,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f100,plain,
    ( spl2_3
    | spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f95,f76,f98,f76])).

fof(f76,plain,
    ( spl2_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ r1_tarski(X0,X1)
        | v1_xboole_0(sK0) )
    | spl2_3 ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X1,sK0)
        | ~ m1_subset_1(X0,sK0)
        | ~ r1_tarski(X0,X1)
        | v1_xboole_0(sK0) )
    | spl2_3 ),
    inference(resolution,[],[f93,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f79,f46])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f49,f46])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),X0,X1)
        | r1_orders_2(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X1,sK0) )
    | spl2_3 ),
    inference(resolution,[],[f92,f77])).

fof(f77,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r3_orders_2(k2_yellow_1(X1),X2,X0)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(global_subsumption,[],[f45,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r3_orders_2(k2_yellow_1(X1),X2,X0)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(k2_yellow_1(X1)) ) ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | ~ r3_orders_2(k2_yellow_1(X1),X2,X0)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(forward_demodulation,[],[f89,f46])).

% (27663)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r3_orders_2(k2_yellow_1(X1),X2,X0)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | ~ l1_struct_0(k2_yellow_1(X1))
      | v1_xboole_0(u1_struct_0(k2_yellow_1(X1))) ) ),
    inference(resolution,[],[f88,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f45,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f86,f46])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f85,f46])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f63,f43])).

fof(f43,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f78,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))
    & r2_hidden(k1_xboole_0,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))
      & r2_hidden(k1_xboole_0,sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f74,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f41,f68])).

fof(f41,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:43:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (27650)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (27665)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (27671)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (27665)Refutation not found, incomplete strategy% (27665)------------------------------
% 0.21/0.49  % (27665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27650)Refutation not found, incomplete strategy% (27650)------------------------------
% 0.21/0.49  % (27650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27650)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (27650)Memory used [KB]: 10618
% 0.21/0.49  % (27650)Time elapsed: 0.065 s
% 0.21/0.49  % (27650)------------------------------
% 0.21/0.49  % (27650)------------------------------
% 0.21/0.49  % (27665)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (27665)Memory used [KB]: 1663
% 0.21/0.49  % (27665)Time elapsed: 0.008 s
% 0.21/0.49  % (27665)------------------------------
% 0.21/0.49  % (27665)------------------------------
% 0.21/0.49  % (27656)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (27656)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f70,f74,f78,f100,f127,f130,f198,f204,f219])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ~spl2_7 | spl2_1 | ~spl2_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f208,f202,f68,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl2_7 <=> l1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl2_1 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl2_20 <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~spl2_20),
% 0.21/0.50    inference(superposition,[],[f51,f203])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~spl2_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f202])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ~spl2_7 | spl2_20 | ~spl2_8 | ~spl2_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f200,f196,f118,f202,f115])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl2_8 <=> m1_subset_1(k1_xboole_0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    spl2_19 <=> ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,sK0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~l1_orders_2(k2_yellow_1(sK0)) | ~spl2_19),
% 0.21/0.50    inference(forward_demodulation,[],[f199,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~spl2_19),
% 0.21/0.50    inference(resolution,[],[f197,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0)) ) | ~spl2_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f196])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ~spl2_8 | spl2_19 | ~spl2_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f193,f98,f196,f118])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl2_4 <=> ! [X1,X0] : (r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),X0) | ~m1_subset_1(k1_xboole_0,sK0)) ) | ~spl2_4),
% 0.21/0.50    inference(resolution,[],[f192,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,sK1(k2_yellow_1(sK0),X0,X1)) | ~r2_lattice3(k2_yellow_1(sK0),X1,X0) | k1_yellow_0(k2_yellow_1(sK0),X1) = X0 | ~m1_subset_1(X0,sK0)) ) | ~spl2_4),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f191])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~r2_lattice3(k2_yellow_1(sK0),X1,X0) | k1_yellow_0(k2_yellow_1(sK0),X1) = X0 | ~r2_lattice3(k2_yellow_1(sK0),X1,X0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X0,sK1(k2_yellow_1(sK0),X0,X1)) | k1_yellow_0(k2_yellow_1(sK0),X1) = X0 | ~m1_subset_1(X0,sK0)) ) | ~spl2_4),
% 0.21/0.50    inference(resolution,[],[f190,f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X2,sK1(k2_yellow_1(sK0),X1,X0)) | ~r2_lattice3(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X1,sK0) | ~r1_tarski(X2,sK1(k2_yellow_1(sK0),X1,X0)) | k1_yellow_0(k2_yellow_1(sK0),X0) = X1 | ~m1_subset_1(X2,sK0)) ) | ~spl2_4),
% 0.21/0.50    inference(resolution,[],[f134,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,sK0) | ~r1_tarski(X0,X1) | r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0)) ) | ~spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k1_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(global_subsumption,[],[f44,f45,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k1_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.50    inference(superposition,[],[f56,f46])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.50    inference(rectify,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2)) | ~m1_subset_1(X1,X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.21/0.50    inference(global_subsumption,[],[f45,f189])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2)) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~l1_orders_2(k2_yellow_1(X0)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.21/0.50    inference(forward_demodulation,[],[f188,f46])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2)) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.21/0.50    inference(resolution,[],[f58,f44])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k1_yellow_0(X0,X2) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ~spl2_2 | spl2_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f128,f118,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl2_2 <=> r2_hidden(k1_xboole_0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ~r2_hidden(k1_xboole_0,sK0) | spl2_8),
% 0.21/0.50    inference(resolution,[],[f119,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,sK0) | spl2_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f118])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl2_7),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    $false | spl2_7),
% 0.21/0.50    inference(resolution,[],[f116,f45])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ~l1_orders_2(k2_yellow_1(sK0)) | spl2_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl2_3 | spl2_4 | spl2_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f95,f76,f98,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl2_3 <=> v1_xboole_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~r1_tarski(X0,X1) | v1_xboole_0(sK0)) ) | spl2_3),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X1,sK0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X0,X1) | v1_xboole_0(sK0)) ) | spl2_3),
% 0.21/0.50    inference(resolution,[],[f93,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f79,f46])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f49,f46])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r3_orders_2(k2_yellow_1(sK0),X0,X1) | r1_orders_2(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(X1,sK0)) ) | spl2_3),
% 0.21/0.50    inference(resolution,[],[f92,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~v1_xboole_0(sK0) | spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~r3_orders_2(k2_yellow_1(X1),X2,X0) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.50    inference(global_subsumption,[],[f45,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~r3_orders_2(k2_yellow_1(X1),X2,X0) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1) | ~l1_orders_2(k2_yellow_1(X1))) )),
% 0.21/0.50    inference(resolution,[],[f90,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_struct_0(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | ~r3_orders_2(k2_yellow_1(X1),X2,X0) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f89,f46])).
% 0.21/0.50  % (27663)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~r3_orders_2(k2_yellow_1(X1),X2,X0) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | ~l1_struct_0(k2_yellow_1(X1)) | v1_xboole_0(u1_struct_0(k2_yellow_1(X1)))) )),
% 0.21/0.50    inference(resolution,[],[f88,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(global_subsumption,[],[f45,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~l1_orders_2(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f86,f46])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f85,f46])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.50    inference(resolution,[],[f63,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ~spl2_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f76])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ~v1_xboole_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k1_xboole_0,sK0) & ~v1_xboole_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k1_xboole_0,sK0) & ~v1_xboole_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f72])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    r2_hidden(k1_xboole_0,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f68])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (27656)------------------------------
% 0.21/0.50  % (27656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27656)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (27656)Memory used [KB]: 10746
% 0.21/0.50  % (27656)Time elapsed: 0.015 s
% 0.21/0.50  % (27656)------------------------------
% 0.21/0.50  % (27656)------------------------------
% 0.21/0.50  % (27663)Refutation not found, incomplete strategy% (27663)------------------------------
% 0.21/0.50  % (27663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27663)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (27663)Memory used [KB]: 6140
% 0.21/0.50  % (27663)Time elapsed: 0.063 s
% 0.21/0.50  % (27663)------------------------------
% 0.21/0.50  % (27663)------------------------------
% 0.21/0.50  % (27644)Success in time 0.14 s
%------------------------------------------------------------------------------
