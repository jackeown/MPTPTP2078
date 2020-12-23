%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 189 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :   24
%              Number of atoms          :  454 ( 732 expanded)
%              Number of equality atoms :   49 (  98 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f79,f131,f141,f152,f158,f160,f188])).

fof(f188,plain,
    ( ~ spl2_10
    | spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f180,f128,f69,f156])).

fof(f156,plain,
    ( spl2_10
  <=> l1_orders_2(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f69,plain,
    ( spl2_1
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f128,plain,
    ( spl2_5
  <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f180,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ spl2_5 ),
    inference(superposition,[],[f50,f129])).

fof(f129,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f50,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f160,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl2_10 ),
    inference(resolution,[],[f157,f44])).

fof(f44,plain,(
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

fof(f157,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( ~ spl2_10
    | ~ spl2_6
    | spl2_7 ),
    inference(avatar_split_clause,[],[f154,f139,f136,f156])).

fof(f136,plain,
    ( spl2_6
  <=> m1_subset_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f139,plain,
    ( spl2_7
  <=> r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f154,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | spl2_7 ),
    inference(forward_demodulation,[],[f153,f45])).

fof(f45,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f153,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | spl2_7 ),
    inference(resolution,[],[f140,f51])).

fof(f51,plain,(
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
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f140,plain,
    ( ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f152,plain,
    ( spl2_3
    | ~ spl2_2
    | spl2_6 ),
    inference(avatar_split_clause,[],[f150,f136,f73,f77])).

fof(f77,plain,
    ( spl2_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f73,plain,
    ( spl2_2
  <=> r2_hidden(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f150,plain,
    ( ~ r2_hidden(k1_xboole_0,sK0)
    | v1_xboole_0(sK0)
    | spl2_6 ),
    inference(resolution,[],[f137,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f137,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f141,plain,
    ( ~ spl2_6
    | ~ spl2_7
    | spl2_5
    | spl2_4 ),
    inference(avatar_split_clause,[],[f132,f125,f128,f139,f136])).

fof(f125,plain,
    ( spl2_4
  <=> m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f132,plain,
    ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,sK0)
    | spl2_4 ),
    inference(resolution,[],[f126,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f43,f44,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f54,f45])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
        & r2_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f43,plain,(
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

fof(f126,plain,
    ( ~ m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f131,plain,
    ( ~ spl2_4
    | spl2_5
    | spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f121,f73,f77,f128,f125])).

fof(f121,plain,
    ( v1_xboole_0(sK0)
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f120,f74])).

fof(f74,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,k1_xboole_0),X0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,k1_xboole_0),X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f118,f61])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,k1_xboole_0),X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(global_subsumption,[],[f44,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,k1_xboole_0),X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f116,f45])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,k1_xboole_0),X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f115,f51])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,X1),X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),X1)
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),X1)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,X1),X0)
      | v1_xboole_0(X0)
      | ~ r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f112,f61])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),X1)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,X1),X0)
      | v1_xboole_0(X0)
      | ~ r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) ) ),
    inference(resolution,[],[f111,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1))
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | v1_xboole_0(X0)
      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f101,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f80,f45])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f49,f45])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X1),X0,sK1(k2_yellow_1(X1),X0,X2))
      | ~ r2_lattice3(k2_yellow_1(X1),X2,X0)
      | k1_yellow_0(k2_yellow_1(X1),X2) = X0
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(sK1(k2_yellow_1(X1),X0,X2),X1)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r2_lattice3(k2_yellow_1(X1),X2,X0)
      | k1_yellow_0(k2_yellow_1(X1),X2) = X0
      | ~ r3_orders_2(k2_yellow_1(X1),X0,sK1(k2_yellow_1(X1),X0,X2))
      | ~ m1_subset_1(sK1(k2_yellow_1(X1),X0,X2),X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f99,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f89,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f42,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f87,f45])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f86,f45])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f42,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2))
      | ~ m1_subset_1(X1,X0)
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(global_subsumption,[],[f44,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2))
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(forward_demodulation,[],[f97,f45])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2))
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f38,f77])).

fof(f38,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))
    & r2_hidden(k1_xboole_0,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f31])).

fof(f31,plain,
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f75,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f39,f73])).

fof(f39,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f40,f69])).

fof(f40,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (11624)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.44  % (11624)Refutation not found, incomplete strategy% (11624)------------------------------
% 0.21/0.44  % (11624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (11634)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.45  % (11624)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (11624)Memory used [KB]: 10618
% 0.21/0.45  % (11624)Time elapsed: 0.041 s
% 0.21/0.45  % (11624)------------------------------
% 0.21/0.45  % (11624)------------------------------
% 0.21/0.45  % (11634)Refutation not found, incomplete strategy% (11634)------------------------------
% 0.21/0.45  % (11634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (11634)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (11634)Memory used [KB]: 10618
% 0.21/0.45  % (11634)Time elapsed: 0.006 s
% 0.21/0.45  % (11634)------------------------------
% 0.21/0.45  % (11634)------------------------------
% 0.21/0.46  % (11629)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (11629)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f71,f75,f79,f131,f141,f152,f158,f160,f188])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    ~spl2_10 | spl2_1 | ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f180,f128,f69,f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    spl2_10 <=> l1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl2_1 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl2_5 <=> k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~spl2_5),
% 0.21/0.47    inference(superposition,[],[f50,f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f128])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    spl2_10),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    $false | spl2_10),
% 0.21/0.47    inference(resolution,[],[f157,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ~l1_orders_2(k2_yellow_1(sK0)) | spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f156])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    ~spl2_10 | ~spl2_6 | spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f154,f139,f136,f156])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    spl2_6 <=> m1_subset_1(k1_xboole_0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    spl2_7 <=> r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    ~m1_subset_1(k1_xboole_0,sK0) | ~l1_orders_2(k2_yellow_1(sK0)) | spl2_7),
% 0.21/0.47    inference(forward_demodulation,[],[f153,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | spl2_7),
% 0.21/0.47    inference(resolution,[],[f140,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0) | spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f139])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl2_3 | ~spl2_2 | spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f150,f136,f73,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl2_3 <=> v1_xboole_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl2_2 <=> r2_hidden(k1_xboole_0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ~r2_hidden(k1_xboole_0,sK0) | v1_xboole_0(sK0) | spl2_6),
% 0.21/0.47    inference(resolution,[],[f137,f61])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ~m1_subset_1(k1_xboole_0,sK0) | spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f136])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~spl2_6 | ~spl2_7 | spl2_5 | spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f132,f125,f128,f139,f136])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    spl2_4 <=> m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,sK0) | spl2_4),
% 0.21/0.47    inference(resolution,[],[f126,f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k1_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.47    inference(global_subsumption,[],[f43,f44,f95])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k1_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(superposition,[],[f54,f45])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.47    inference(rectify,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ~m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0) | spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f125])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~spl2_4 | spl2_5 | spl2_3 | ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f121,f73,f77,f128,f125])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    v1_xboole_0(sK0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0) | ~spl2_2),
% 0.21/0.47    inference(resolution,[],[f120,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    r2_hidden(k1_xboole_0,sK0) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) | ~m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,k1_xboole_0),X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f119])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,k1_xboole_0),X0) | v1_xboole_0(X0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) | ~r2_hidden(k1_xboole_0,X0) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(resolution,[],[f118,f61])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,k1_xboole_0),X0) | v1_xboole_0(X0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) | ~r2_hidden(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(global_subsumption,[],[f44,f117])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,k1_xboole_0),X0) | v1_xboole_0(X0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) | ~r2_hidden(k1_xboole_0,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f116,f45])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,k1_xboole_0),X0) | v1_xboole_0(X0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) | ~r2_hidden(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(resolution,[],[f115,f51])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) | ~m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,X1),X0) | v1_xboole_0(X0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),X1) | ~r2_hidden(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),X1) | ~m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,X1),X0) | v1_xboole_0(X0) | ~r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(resolution,[],[f112,f61])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,X0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),X1) | ~m1_subset_1(sK1(k2_yellow_1(X0),k1_xboole_0,X1),X0) | v1_xboole_0(X0) | ~r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0)) )),
% 0.21/0.47    inference(resolution,[],[f111,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~m1_subset_1(X2,X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | v1_xboole_0(X0) | ~r2_lattice3(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~m1_subset_1(X2,X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | v1_xboole_0(X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~m1_subset_1(X2,X0) | ~r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(resolution,[],[f101,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f80,f45])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f49,f45])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X1),X0,sK1(k2_yellow_1(X1),X0,X2)) | ~r2_lattice3(k2_yellow_1(X1),X2,X0) | k1_yellow_0(k2_yellow_1(X1),X2) = X0 | ~m1_subset_1(X0,X1) | ~m1_subset_1(sK1(k2_yellow_1(X1),X0,X2),X1) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f100])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~r2_lattice3(k2_yellow_1(X1),X2,X0) | k1_yellow_0(k2_yellow_1(X1),X2) = X0 | ~r3_orders_2(k2_yellow_1(X1),X0,sK1(k2_yellow_1(X1),X0,X2)) | ~m1_subset_1(sK1(k2_yellow_1(X1),X0,X2),X1) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(resolution,[],[f99,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X1),X2,X0) | ~r3_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(resolution,[],[f89,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.47    inference(global_subsumption,[],[f42,f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f87,f45])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f86,f45])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(resolution,[],[f64,f44])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2)) | ~m1_subset_1(X1,X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.21/0.47    inference(global_subsumption,[],[f44,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2)) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~l1_orders_2(k2_yellow_1(X0)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.21/0.47    inference(forward_demodulation,[],[f97,f45])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2)) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.21/0.47    inference(resolution,[],[f56,f43])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,X1,sK1(X0,X1,X2)) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k1_yellow_0(X0,X2) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f77])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k1_xboole_0,sK0) & ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k1_xboole_0,sK0) & ~v1_xboole_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f73])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    r2_hidden(k1_xboole_0,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f69])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (11629)------------------------------
% 0.21/0.47  % (11629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11629)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (11629)Memory used [KB]: 10746
% 0.21/0.47  % (11629)Time elapsed: 0.062 s
% 0.21/0.47  % (11629)------------------------------
% 0.21/0.47  % (11629)------------------------------
% 0.21/0.47  % (11621)Success in time 0.117 s
%------------------------------------------------------------------------------
