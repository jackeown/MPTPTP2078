%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 388 expanded)
%              Number of leaves         :   27 ( 122 expanded)
%              Depth                    :   32
%              Number of atoms          :  572 (1313 expanded)
%              Number of equality atoms :   56 ( 168 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f95,f101,f117,f138,f177,f192,f201,f206,f211,f217,f221])).

fof(f221,plain,
    ( ~ spl3_4
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f219,f100])).

fof(f100,plain,
    ( m1_subset_1(k1_xboole_0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_4
  <=> m1_subset_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f219,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | spl3_10 ),
    inference(forward_demodulation,[],[f218,f53])).

fof(f53,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f218,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | spl3_10 ),
    inference(subsumption_resolution,[],[f214,f52])).

fof(f52,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f214,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ l1_orders_2(k2_yellow_1(sK1))
    | spl3_10 ),
    inference(resolution,[],[f200,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f200,plain,
    ( ~ r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl3_10
  <=> r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f217,plain,
    ( ~ spl3_4
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f215,f100])).

fof(f215,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | spl3_10 ),
    inference(forward_demodulation,[],[f213,f53])).

fof(f213,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f52,f200,f60])).

fof(f211,plain,
    ( ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f209,f100])).

fof(f209,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | spl3_9 ),
    inference(forward_demodulation,[],[f208,f53])).

fof(f208,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | spl3_9 ),
    inference(subsumption_resolution,[],[f207,f51])).

fof(f51,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f207,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ v5_orders_2(k2_yellow_1(sK1))
    | spl3_9 ),
    inference(subsumption_resolution,[],[f203,f52])).

fof(f203,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ l1_orders_2(k2_yellow_1(sK1))
    | ~ v5_orders_2(k2_yellow_1(sK1))
    | spl3_9 ),
    inference(resolution,[],[f196,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X2,X0,X1)
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X2,X0,X1)
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
    inference(definition_folding,[],[f31,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ( r1_yellow_0(X0,X2)
        & k1_yellow_0(X0,X2) = X1 )
      | ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ r2_lattice3(X0,X2,X1)
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(rectify,[],[f8])).

fof(f8,axiom,(
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

fof(f196,plain,
    ( ~ sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl3_9
  <=> sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f206,plain,
    ( ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f204,f100])).

fof(f204,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | spl3_9 ),
    inference(forward_demodulation,[],[f202,f53])).

fof(f202,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f51,f52,f196,f70])).

fof(f201,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | spl3_3
    | spl3_7 ),
    inference(avatar_split_clause,[],[f185,f174,f92,f198,f194])).

fof(f92,plain,
    ( spl3_3
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f174,plain,
    ( spl3_7
  <=> m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f185,plain,
    ( ~ r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)
    | ~ sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)
    | spl3_3
    | spl3_7 ),
    inference(subsumption_resolution,[],[f184,f94])).

fof(f94,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f184,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1))
    | ~ r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)
    | ~ sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)
    | spl3_7 ),
    inference(forward_demodulation,[],[f180,f111])).

fof(f111,plain,(
    ! [X0] : k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f52,f59])).

fof(f59,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f180,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | ~ r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)
    | ~ sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)
    | spl3_7 ),
    inference(resolution,[],[f176,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X1,k2_yellow_1(X0),X2),X0)
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ sP0(X1,k2_yellow_1(X0),X2) ) ),
    inference(superposition,[],[f62,f53])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | k1_yellow_0(X1,X0) = X2
      | ~ r2_lattice3(X1,X0,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_yellow_0(X1,X0)
        & k1_yellow_0(X1,X0) = X2 )
      | ( ~ r1_orders_2(X1,X2,sK2(X0,X1,X2))
        & r2_lattice3(X1,X0,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
      | ~ r2_lattice3(X1,X0,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X2,X3)
          & r2_lattice3(X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X2,sK2(X0,X1,X2))
        & r2_lattice3(X1,X0,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_yellow_0(X1,X0)
        & k1_yellow_0(X1,X0) = X2 )
      | ? [X3] :
          ( ~ r1_orders_2(X1,X2,X3)
          & r2_lattice3(X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
      | ~ r2_lattice3(X1,X0,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ( r1_yellow_0(X0,X2)
        & k1_yellow_0(X0,X2) = X1 )
      | ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ r2_lattice3(X0,X2,X1)
      | ~ sP0(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f176,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f174])).

fof(f192,plain,
    ( ~ spl3_8
    | spl3_7 ),
    inference(avatar_split_clause,[],[f178,f174,f189])).

fof(f189,plain,
    ( spl3_8
  <=> r2_hidden(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f178,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f176,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f177,plain,
    ( ~ spl3_7
    | spl3_1
    | spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f172,f98,f92,f81,f174])).

fof(f81,plain,
    ( spl3_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f172,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)
    | spl3_1
    | spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f171,f100])).

fof(f171,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)
    | spl3_1
    | spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f170,f53])).

fof(f170,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | spl3_1
    | spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f169,f94])).

fof(f169,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1))
    | ~ m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f168,f111])).

fof(f168,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f167,f52])).

fof(f167,plain,
    ( ~ m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1)))
    | ~ l1_orders_2(k2_yellow_1(sK1))
    | spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f166,f60])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0)
        | ~ m1_subset_1(sK2(X0,k2_yellow_1(sK1),k1_xboole_0),sK1)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),X0) )
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f164,f100])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,sK1)
        | ~ m1_subset_1(sK2(X0,k2_yellow_1(sK1),k1_xboole_0),sK1)
        | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),X0) )
    | spl3_1 ),
    inference(resolution,[],[f158,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK2(X0,k2_yellow_1(sK1),X1))
        | ~ r2_lattice3(k2_yellow_1(sK1),X0,X1)
        | ~ m1_subset_1(X1,sK1)
        | ~ m1_subset_1(sK2(X0,k2_yellow_1(sK1),X1),sK1)
        | k1_yellow_0(k2_yellow_1(sK1),X0) = X1 )
    | spl3_1 ),
    inference(subsumption_resolution,[],[f157,f83])).

fof(f83,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( k1_yellow_0(k2_yellow_1(sK1),X0) = X1
        | ~ r2_lattice3(k2_yellow_1(sK1),X0,X1)
        | ~ m1_subset_1(X1,sK1)
        | ~ m1_subset_1(sK2(X0,k2_yellow_1(sK1),X1),sK1)
        | ~ r1_tarski(X1,sK2(X0,k2_yellow_1(sK1),X1))
        | v1_xboole_0(sK1) )
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( k1_yellow_0(k2_yellow_1(sK1),X0) = X1
        | ~ r2_lattice3(k2_yellow_1(sK1),X0,X1)
        | ~ m1_subset_1(X1,sK1)
        | ~ m1_subset_1(sK2(X0,k2_yellow_1(sK1),X1),sK1)
        | ~ m1_subset_1(X1,sK1)
        | ~ r1_tarski(X1,sK2(X0,k2_yellow_1(sK1),X1))
        | v1_xboole_0(sK1) )
    | spl3_1 ),
    inference(resolution,[],[f154,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f76,f53])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f56,f53])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0))
        | k1_yellow_0(k2_yellow_1(sK1),X1) = X0
        | ~ r2_lattice3(k2_yellow_1(sK1),X1,X0)
        | ~ m1_subset_1(X0,sK1) )
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X0,sK1)
        | k1_yellow_0(k2_yellow_1(sK1),X1) = X0
        | ~ r2_lattice3(k2_yellow_1(sK1),X1,X0)
        | ~ r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0)) )
    | spl3_1 ),
    inference(forward_demodulation,[],[f152,f53])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_yellow_0(k2_yellow_1(sK1),X1) = X0
        | ~ r2_lattice3(k2_yellow_1(sK1),X1,X0)
        | ~ r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) )
    | spl3_1 ),
    inference(subsumption_resolution,[],[f151,f51])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_yellow_0(k2_yellow_1(sK1),X1) = X0
        | ~ r2_lattice3(k2_yellow_1(sK1),X1,X0)
        | ~ r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
        | ~ v5_orders_2(k2_yellow_1(sK1)) )
    | spl3_1 ),
    inference(subsumption_resolution,[],[f150,f52])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_yellow_0(k2_yellow_1(sK1),X1) = X0
        | ~ r2_lattice3(k2_yellow_1(sK1),X1,X0)
        | ~ r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))
        | ~ l1_orders_2(k2_yellow_1(sK1))
        | ~ v5_orders_2(k2_yellow_1(sK1)) )
    | spl3_1 ),
    inference(resolution,[],[f141,f70])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ sP0(X1,k2_yellow_1(sK1),X0)
        | ~ m1_subset_1(X0,sK1)
        | k1_yellow_0(k2_yellow_1(sK1),X1) = X0
        | ~ r2_lattice3(k2_yellow_1(sK1),X1,X0)
        | ~ r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0)) )
    | spl3_1 ),
    inference(subsumption_resolution,[],[f140,f124])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0))
        | ~ m1_subset_1(sK2(X1,k2_yellow_1(sK1),X0),sK1)
        | ~ m1_subset_1(X0,sK1)
        | k1_yellow_0(k2_yellow_1(sK1),X1) = X0
        | ~ r2_lattice3(k2_yellow_1(sK1),X1,X0)
        | ~ sP0(X1,k2_yellow_1(sK1),X0) )
    | spl3_1 ),
    inference(resolution,[],[f133,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X2,sK2(X0,X1,X2))
      | k1_yellow_0(X1,X0) = X2
      | ~ r2_lattice3(X1,X0,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK1),X1,X0)
        | ~ r3_orders_2(k2_yellow_1(sK1),X1,X0)
        | ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X1,sK1) )
    | spl3_1 ),
    inference(resolution,[],[f131,f83])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | ~ r3_orders_2(k2_yellow_1(X1),X2,X0)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1) ) ),
    inference(forward_demodulation,[],[f130,f105])).

fof(f105,plain,(
    ! [X0] : k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(forward_demodulation,[],[f102,f53])).

fof(f102,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(unit_resulting_resolution,[],[f90,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f90,plain,(
    ! [X0] : l1_struct_0(k2_yellow_1(X0)) ),
    inference(unit_resulting_resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r3_orders_2(k2_yellow_1(X1),X2,X0)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(k2_struct_0(k2_yellow_1(X1))) ) ),
    inference(subsumption_resolution,[],[f129,f90])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r3_orders_2(k2_yellow_1(X1),X2,X0)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1)
      | ~ l1_struct_0(k2_yellow_1(X1))
      | v1_xboole_0(k2_struct_0(k2_yellow_1(X1))) ) ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_struct_0)).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(forward_demodulation,[],[f127,f53])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f126,f53])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f125,f52])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f72,f50])).

fof(f50,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f138,plain,
    ( spl3_6
    | spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f132,f114,f98,f81,f135])).

fof(f135,plain,
    ( spl3_6
  <=> r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f114,plain,
    ( spl3_5
  <=> r3_orders_2(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f132,plain,
    ( r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)
    | spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f83,f100,f100,f116,f131])).

fof(f116,plain,
    ( r3_orders_2(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( spl3_5
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f112,f98,f81,f114])).

fof(f112,plain,
    ( r3_orders_2(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f83,f49,f100,f100,f77])).

fof(f101,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f96,f86,f98])).

fof(f86,plain,
    ( spl3_2
  <=> r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f96,plain,
    ( m1_subset_1(k1_xboole_0,sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f88,f71])).

fof(f88,plain,
    ( r2_hidden(k1_xboole_0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f95,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f48,f92])).

fof(f48,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))
    & r2_hidden(k1_xboole_0,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))
      & r2_hidden(k1_xboole_0,sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f89,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f47,f86])).

fof(f47,plain,(
    r2_hidden(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:45:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.41  % (20185)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (20185)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f84,f89,f95,f101,f117,f138,f177,f192,f201,f206,f211,f217,f221])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    ~spl3_4 | spl3_10),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f220])).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    $false | (~spl3_4 | spl3_10)),
% 0.20/0.47    inference(subsumption_resolution,[],[f219,f100])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    m1_subset_1(k1_xboole_0,sK1) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl3_4 <=> m1_subset_1(k1_xboole_0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,sK1) | spl3_10),
% 0.20/0.47    inference(forward_demodulation,[],[f218,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.47  fof(f218,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | spl3_10),
% 0.20/0.47    inference(subsumption_resolution,[],[f214,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | ~l1_orders_2(k2_yellow_1(sK1)) | spl3_10),
% 0.20/0.47    inference(resolution,[],[f200,f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    ~r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) | spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f198])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    spl3_10 <=> r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    ~spl3_4 | spl3_10),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f216])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    $false | (~spl3_4 | spl3_10)),
% 0.20/0.47    inference(subsumption_resolution,[],[f215,f100])).
% 0.20/0.47  fof(f215,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,sK1) | spl3_10),
% 0.20/0.47    inference(forward_demodulation,[],[f213,f53])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | spl3_10),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f52,f200,f60])).
% 0.20/0.47  fof(f211,plain,(
% 0.20/0.47    ~spl3_4 | spl3_9),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f210])).
% 0.20/0.47  fof(f210,plain,(
% 0.20/0.47    $false | (~spl3_4 | spl3_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f209,f100])).
% 0.20/0.47  fof(f209,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,sK1) | spl3_9),
% 0.20/0.47    inference(forward_demodulation,[],[f208,f53])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | spl3_9),
% 0.20/0.47    inference(subsumption_resolution,[],[f207,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.47    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | ~v5_orders_2(k2_yellow_1(sK1)) | spl3_9),
% 0.20/0.47    inference(subsumption_resolution,[],[f203,f52])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | ~l1_orders_2(k2_yellow_1(sK1)) | ~v5_orders_2(k2_yellow_1(sK1)) | spl3_9),
% 0.20/0.47    inference(resolution,[],[f196,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (sP0(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (sP0(X2,X0,X1) & ((! [X3] : (r1_orders_2(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.47    inference(rectify,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (sP0(X2,X0,X1) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.47    inference(definition_folding,[],[f31,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X2,X0,X1] : ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1) | ~sP0(X2,X0,X1))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.47    inference(flattening,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.20/0.47    inference(rectify,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    ~sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0) | spl3_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f194])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    spl3_9 <=> sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    ~spl3_4 | spl3_9),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f205])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    $false | (~spl3_4 | spl3_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f204,f100])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,sK1) | spl3_9),
% 0.20/0.47    inference(forward_demodulation,[],[f202,f53])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | spl3_9),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f51,f52,f196,f70])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    ~spl3_9 | ~spl3_10 | spl3_3 | spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f185,f174,f92,f198,f194])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl3_3 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    spl3_7 <=> m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f185,plain,(
% 0.20/0.47    ~r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) | ~sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0) | (spl3_3 | spl3_7)),
% 0.20/0.47    inference(subsumption_resolution,[],[f184,f94])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) | spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f92])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) | ~r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) | ~sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0) | spl3_7),
% 0.20/0.47    inference(forward_demodulation,[],[f180,f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X0] : (k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)) )),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f52,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) | ~r2_lattice3(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) | ~sP0(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0) | spl3_7),
% 0.20/0.47    inference(resolution,[],[f176,f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X1,k2_yellow_1(X0),X2),X0) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~sP0(X1,k2_yellow_1(X0),X2)) )),
% 0.20/0.47    inference(superposition,[],[f62,f53])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | k1_yellow_0(X1,X0) = X2 | ~r2_lattice3(X1,X0,X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_yellow_0(X1,X0) & k1_yellow_0(X1,X0) = X2) | (~r1_orders_2(X1,X2,sK2(X0,X1,X2)) & r2_lattice3(X1,X0,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))) | ~r2_lattice3(X1,X0,X2) | ~sP0(X0,X1,X2))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X2,X3) & r2_lattice3(X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,X2,sK2(X0,X1,X2)) & r2_lattice3(X1,X0,sK2(X0,X1,X2)) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_yellow_0(X1,X0) & k1_yellow_0(X1,X0) = X2) | ? [X3] : (~r1_orders_2(X1,X2,X3) & r2_lattice3(X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_lattice3(X1,X0,X2) | ~sP0(X0,X1,X2))),
% 0.20/0.47    inference(rectify,[],[f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ! [X2,X0,X1] : ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1) | ~sP0(X2,X0,X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f35])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ~m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) | spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f174])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    ~spl3_8 | spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f178,f174,f189])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    spl3_8 <=> r2_hidden(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ~r2_hidden(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) | spl3_7),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f176,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ~spl3_7 | spl3_1 | spl3_3 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f172,f98,f92,f81,f174])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl3_1 <=> v1_xboole_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ~m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) | (spl3_1 | spl3_3 | ~spl3_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f171,f100])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ~m1_subset_1(k1_xboole_0,sK1) | ~m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) | (spl3_1 | spl3_3 | ~spl3_4)),
% 0.20/0.47    inference(forward_demodulation,[],[f170,f53])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    ~m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | (spl3_1 | spl3_3 | ~spl3_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f169,f94])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK1)) | ~m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | (spl3_1 | ~spl3_4)),
% 0.20/0.47    inference(forward_demodulation,[],[f168,f111])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    ~m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | (spl3_1 | ~spl3_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f167,f52])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    ~m1_subset_1(sK2(k1_xboole_0,k2_yellow_1(sK1),k1_xboole_0),sK1) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK1))) | ~l1_orders_2(k2_yellow_1(sK1)) | (spl3_1 | ~spl3_4)),
% 0.20/0.47    inference(resolution,[],[f166,f60])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) | ~m1_subset_1(sK2(X0,k2_yellow_1(sK1),k1_xboole_0),sK1) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),X0)) ) | (spl3_1 | ~spl3_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f164,f100])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_lattice3(k2_yellow_1(sK1),X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,sK1) | ~m1_subset_1(sK2(X0,k2_yellow_1(sK1),k1_xboole_0),sK1) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK1),X0)) ) | spl3_1),
% 0.20/0.47    inference(resolution,[],[f158,f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X1,sK2(X0,k2_yellow_1(sK1),X1)) | ~r2_lattice3(k2_yellow_1(sK1),X0,X1) | ~m1_subset_1(X1,sK1) | ~m1_subset_1(sK2(X0,k2_yellow_1(sK1),X1),sK1) | k1_yellow_0(k2_yellow_1(sK1),X0) = X1) ) | spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f157,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f81])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_yellow_0(k2_yellow_1(sK1),X0) = X1 | ~r2_lattice3(k2_yellow_1(sK1),X0,X1) | ~m1_subset_1(X1,sK1) | ~m1_subset_1(sK2(X0,k2_yellow_1(sK1),X1),sK1) | ~r1_tarski(X1,sK2(X0,k2_yellow_1(sK1),X1)) | v1_xboole_0(sK1)) ) | spl3_1),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f155])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_yellow_0(k2_yellow_1(sK1),X0) = X1 | ~r2_lattice3(k2_yellow_1(sK1),X0,X1) | ~m1_subset_1(X1,sK1) | ~m1_subset_1(sK2(X0,k2_yellow_1(sK1),X1),sK1) | ~m1_subset_1(X1,sK1) | ~r1_tarski(X1,sK2(X0,k2_yellow_1(sK1),X1)) | v1_xboole_0(sK1)) ) | spl3_1),
% 0.20/0.47    inference(resolution,[],[f154,f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f76,f53])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f56,f53])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0)) | k1_yellow_0(k2_yellow_1(sK1),X1) = X0 | ~r2_lattice3(k2_yellow_1(sK1),X1,X0) | ~m1_subset_1(X0,sK1)) ) | spl3_1),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f153])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | ~m1_subset_1(X0,sK1) | k1_yellow_0(k2_yellow_1(sK1),X1) = X0 | ~r2_lattice3(k2_yellow_1(sK1),X1,X0) | ~r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0))) ) | spl3_1),
% 0.20/0.47    inference(forward_demodulation,[],[f152,f53])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | k1_yellow_0(k2_yellow_1(sK1),X1) = X0 | ~r2_lattice3(k2_yellow_1(sK1),X1,X0) | ~r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1)))) ) | spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f151,f51])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | k1_yellow_0(k2_yellow_1(sK1),X1) = X0 | ~r2_lattice3(k2_yellow_1(sK1),X1,X0) | ~r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) | ~v5_orders_2(k2_yellow_1(sK1))) ) | spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f150,f52])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | k1_yellow_0(k2_yellow_1(sK1),X1) = X0 | ~r2_lattice3(k2_yellow_1(sK1),X1,X0) | ~r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK1))) | ~l1_orders_2(k2_yellow_1(sK1)) | ~v5_orders_2(k2_yellow_1(sK1))) ) | spl3_1),
% 0.20/0.47    inference(resolution,[],[f141,f70])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~sP0(X1,k2_yellow_1(sK1),X0) | ~m1_subset_1(X0,sK1) | k1_yellow_0(k2_yellow_1(sK1),X1) = X0 | ~r2_lattice3(k2_yellow_1(sK1),X1,X0) | ~r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0))) ) | spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f140,f124])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r3_orders_2(k2_yellow_1(sK1),X0,sK2(X1,k2_yellow_1(sK1),X0)) | ~m1_subset_1(sK2(X1,k2_yellow_1(sK1),X0),sK1) | ~m1_subset_1(X0,sK1) | k1_yellow_0(k2_yellow_1(sK1),X1) = X0 | ~r2_lattice3(k2_yellow_1(sK1),X1,X0) | ~sP0(X1,k2_yellow_1(sK1),X0)) ) | spl3_1),
% 0.20/0.47    inference(resolution,[],[f133,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_orders_2(X1,X2,sK2(X0,X1,X2)) | k1_yellow_0(X1,X0) = X2 | ~r2_lattice3(X1,X0,X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f43])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK1),X1,X0) | ~r3_orders_2(k2_yellow_1(sK1),X1,X0) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(X1,sK1)) ) | spl3_1),
% 0.20/0.47    inference(resolution,[],[f131,f83])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | ~r3_orders_2(k2_yellow_1(X1),X2,X0) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f130,f105])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ( ! [X0] : (k2_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.47    inference(forward_demodulation,[],[f102,f53])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f90,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X0] : (l1_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f52,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~r3_orders_2(k2_yellow_1(X1),X2,X0) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | v1_xboole_0(k2_struct_0(k2_yellow_1(X1)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f129,f90])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~r3_orders_2(k2_yellow_1(X1),X2,X0) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1) | ~l1_struct_0(k2_yellow_1(X1)) | v1_xboole_0(k2_struct_0(k2_yellow_1(X1)))) )),
% 0.20/0.47    inference(resolution,[],[f128,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(k2_struct_0(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_struct_0)).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f127,f53])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f126,f53])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f125,f52])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.47    inference(resolution,[],[f72,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    spl3_6 | spl3_1 | ~spl3_4 | ~spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f132,f114,f98,f81,f135])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    spl3_6 <=> r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    spl3_5 <=> r3_orders_2(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    r1_orders_2(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) | (spl3_1 | ~spl3_4 | ~spl3_5)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f83,f100,f100,f116,f131])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    r3_orders_2(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f114])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl3_5 | spl3_1 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f112,f98,f81,f114])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    r3_orders_2(k2_yellow_1(sK1),k1_xboole_0,k1_xboole_0) | (spl3_1 | ~spl3_4)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f83,f49,f100,f100,f77])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl3_4 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f96,f86,f98])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl3_2 <=> r2_hidden(k1_xboole_0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    m1_subset_1(k1_xboole_0,sK1) | ~spl3_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f88,f71])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    r2_hidden(k1_xboole_0,sK1) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f92])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) & r2_hidden(k1_xboole_0,sK1) & ~v1_xboole_0(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK1)) & r2_hidden(k1_xboole_0,sK1) & ~v1_xboole_0(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.47    inference(negated_conjecture,[],[f14])).
% 0.20/0.47  fof(f14,conjecture,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f47,f86])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    r2_hidden(k1_xboole_0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f46,f81])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (20185)------------------------------
% 0.20/0.47  % (20185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (20185)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (20185)Memory used [KB]: 1791
% 0.20/0.47  % (20185)Time elapsed: 0.066 s
% 0.20/0.47  % (20185)------------------------------
% 0.20/0.47  % (20185)------------------------------
% 0.20/0.48  % (20177)Success in time 0.127 s
%------------------------------------------------------------------------------
