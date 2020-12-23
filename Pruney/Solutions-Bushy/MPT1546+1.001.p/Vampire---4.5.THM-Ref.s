%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1546+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 334 expanded)
%              Number of leaves         :   14 ( 109 expanded)
%              Depth                    :   20
%              Number of atoms          :  564 (2935 expanded)
%              Number of equality atoms :   45 ( 510 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10583)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f64,f78,f82,f117,f195,f228])).

fof(f228,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f226,f33])).

fof(f33,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_orders_2(sK0,sK2,sK1)
      | sK1 != k13_lattice3(sK0,sK1,sK2) )
    & ( r1_orders_2(sK0,sK2,sK1)
      | sK1 = k13_lattice3(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X2,X1)
                  | k13_lattice3(X0,X1,X2) != X1 )
                & ( r1_orders_2(X0,X2,X1)
                  | k13_lattice3(X0,X1,X2) = X1 )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK0,X2,X1)
                | k13_lattice3(sK0,X1,X2) != X1 )
              & ( r1_orders_2(sK0,X2,X1)
                | k13_lattice3(sK0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_orders_2(sK0,X2,X1)
              | k13_lattice3(sK0,X1,X2) != X1 )
            & ( r1_orders_2(sK0,X2,X1)
              | k13_lattice3(sK0,X1,X2) = X1 )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r1_orders_2(sK0,X2,sK1)
            | sK1 != k13_lattice3(sK0,sK1,X2) )
          & ( r1_orders_2(sK0,X2,sK1)
            | sK1 = k13_lattice3(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ( ~ r1_orders_2(sK0,X2,sK1)
          | sK1 != k13_lattice3(sK0,sK1,X2) )
        & ( r1_orders_2(sK0,X2,sK1)
          | sK1 = k13_lattice3(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r1_orders_2(sK0,sK2,sK1)
        | sK1 != k13_lattice3(sK0,sK1,sK2) )
      & ( r1_orders_2(sK0,sK2,sK1)
        | sK1 = k13_lattice3(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) != X1 )
              & ( r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) != X1 )
              & ( r1_orders_2(X0,X2,X1)
                | k13_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k13_lattice3(X0,X1,X2) = X1
              <~> r1_orders_2(X0,X2,X1) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k13_lattice3(X0,X1,X2) = X1
                <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k13_lattice3(X0,X1,X2) = X1
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_0)).

fof(f226,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f225,f34])).

fof(f34,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f225,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f224,f35])).

fof(f35,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f224,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f223,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f223,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f222,f60])).

fof(f60,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_2
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f222,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f207,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f207,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_1 ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl4_1 ),
    inference(superposition,[],[f53,f62])).

fof(f62,plain,
    ( sK1 = k13_lattice3(sK0,sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_1
  <=> sK1 = k13_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f195,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f193,f33])).

fof(f193,plain,
    ( ~ v5_orders_2(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f192,f34])).

fof(f192,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f191,f35])).

fof(f191,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f190,f37])).

fof(f190,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f189,f36])).

fof(f189,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f188,f116])).

fof(f116,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_6
  <=> r1_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f188,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f184,f63])).

fof(f63,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f184,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f171])).

fof(f171,plain,
    ( sK1 != sK1
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl4_1 ),
    inference(superposition,[],[f57,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,
    ( sK1 != k13_lattice3(sK0,sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f117,plain,
    ( spl4_3
    | spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f113,f73,f115,f70])).

fof(f70,plain,
    ( spl4_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f73,plain,
    ( spl4_4
  <=> ! [X0] :
        ( r3_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f113,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f112,f32])).

fof(f32,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f111,f35])).

fof(f111,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f110,f36])).

fof(f110,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f97,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f97,plain,
    ( r3_orders_2(sK0,sK1,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f74,f36])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X0) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f82,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f80,f35])).

fof(f80,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f79,f34])).

fof(f79,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f71,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f71,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f78,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f77,f73,f70])).

fof(f77,plain,(
    ! [X1] :
      ( r3_orders_2(sK0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f76,f32])).

fof(f76,plain,(
    ! [X1] :
      ( r3_orders_2(sK0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f66,plain,(
    ! [X1] :
      ( r3_orders_2(sK0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f48,f37])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f64,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f38,f59,f56])).

fof(f38,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f39,f59,f56])).

fof(f39,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | sK1 != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

%------------------------------------------------------------------------------
