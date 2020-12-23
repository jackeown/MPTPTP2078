%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1217+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:29 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  263 (1087 expanded)
%              Number of leaves         :   36 ( 395 expanded)
%              Depth                    :   24
%              Number of atoms          : 1223 (7433 expanded)
%              Number of equality atoms :   69 ( 111 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2553,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f119,f130,f135,f170,f175,f178,f254,f259,f264,f334,f341,f363,f424,f429,f2451,f2469,f2499,f2550])).

fof(f2550,plain,
    ( ~ spl4_4
    | ~ spl4_24
    | ~ spl4_134 ),
    inference(avatar_contradiction_clause,[],[f2549])).

fof(f2549,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_24
    | ~ spl4_134 ),
    inference(subsumption_resolution,[],[f2548,f65])).

fof(f65,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f52,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1))
              & r3_lattices(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1))
            & r3_lattices(sK0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1))
          & r3_lattices(sK0,sK1,X2)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X2] :
        ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1))
        & r3_lattices(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
      & r3_lattices(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                 => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).

fof(f2548,plain,
    ( r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_24
    | ~ spl4_134 ),
    inference(subsumption_resolution,[],[f2547,f400])).

fof(f400,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl4_24
  <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f2547,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_24
    | ~ spl4_134 ),
    inference(subsumption_resolution,[],[f2546,f62])).

fof(f62,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f2546,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_24
    | ~ spl4_134 ),
    inference(trivial_inequality_removal,[],[f2541])).

fof(f2541,plain,
    ( k5_lattices(sK0) != k5_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_24
    | ~ spl4_134 ),
    inference(superposition,[],[f227,f2514])).

fof(f2514,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl4_24
    | ~ spl4_134 ),
    inference(subsumption_resolution,[],[f2513,f62])).

fof(f2513,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_24
    | ~ spl4_134 ),
    inference(subsumption_resolution,[],[f2505,f400])).

fof(f2505,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_134 ),
    inference(superposition,[],[f2450,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f104,f61])).

fof(f61,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f103,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) = k2_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f100,f59])).

fof(f59,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f97,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k4_lattices(X1,X2,X0) = k2_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f94,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f2450,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl4_134 ),
    inference(avatar_component_clause,[],[f2448])).

fof(f2448,plain,
    ( spl4_134
  <=> k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f227,plain,
    ( ! [X2,X3] :
        ( k4_lattices(sK0,X3,X2) != k5_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_lattices(sK0,X2,k7_lattices(sK0,X3)) )
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,
    ( ! [X2,X3] :
        ( k4_lattices(sK0,X3,X2) != k5_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_lattices(sK0,X2,k7_lattices(sK0,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl4_4 ),
    inference(superposition,[],[f222,f129])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f222,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) != k5_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X0,k7_lattices(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f221,f58])).

fof(f221,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) != k5_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f220,f59])).

fof(f220,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) != k5_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f219,f61])).

fof(f219,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) != k5_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f85,f60])).

fof(f60,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | k4_lattices(X0,X1,X2) != k5_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                  | ~ r3_lattices(X0,X1,k7_lattices(X0,X2)) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).

fof(f2499,plain,
    ( ~ spl4_10
    | ~ spl4_131
    | spl4_133 ),
    inference(avatar_contradiction_clause,[],[f2498])).

fof(f2498,plain,
    ( $false
    | ~ spl4_10
    | ~ spl4_131
    | spl4_133 ),
    inference(subsumption_resolution,[],[f2497,f58])).

fof(f2497,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_10
    | ~ spl4_131
    | spl4_133 ),
    inference(subsumption_resolution,[],[f2496,f59])).

fof(f2496,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_10
    | ~ spl4_131
    | spl4_133 ),
    inference(subsumption_resolution,[],[f2495,f202])).

fof(f202,plain,
    ( v13_lattices(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl4_10
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f2495,plain,
    ( ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_131
    | spl4_133 ),
    inference(subsumption_resolution,[],[f2494,f61])).

fof(f2494,plain,
    ( ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_131
    | spl4_133 ),
    inference(subsumption_resolution,[],[f2492,f2433])).

fof(f2433,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl4_131 ),
    inference(avatar_component_clause,[],[f2432])).

fof(f2432,plain,
    ( spl4_131
  <=> m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).

fof(f2492,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_133 ),
    inference(resolution,[],[f2446,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r3_lattices(X0,k5_lattices(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattices)).

fof(f2446,plain,
    ( ~ r3_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl4_133 ),
    inference(avatar_component_clause,[],[f2444])).

fof(f2444,plain,
    ( spl4_133
  <=> r3_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_133])])).

fof(f2469,plain,
    ( ~ spl4_1
    | ~ spl4_24
    | spl4_131 ),
    inference(avatar_contradiction_clause,[],[f2468])).

fof(f2468,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_24
    | spl4_131 ),
    inference(subsumption_resolution,[],[f2467,f58])).

fof(f2467,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_24
    | spl4_131 ),
    inference(subsumption_resolution,[],[f2466,f111])).

fof(f111,plain,
    ( l1_lattices(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_1
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2466,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_24
    | spl4_131 ),
    inference(subsumption_resolution,[],[f2465,f62])).

fof(f2465,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_24
    | spl4_131 ),
    inference(subsumption_resolution,[],[f2463,f400])).

fof(f2463,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_131 ),
    inference(resolution,[],[f2434,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f2434,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | spl4_131 ),
    inference(avatar_component_clause,[],[f2432])).

fof(f2451,plain,
    ( ~ spl4_131
    | ~ spl4_133
    | spl4_134
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f2442,f403,f399,f205,f168,f2448,f2444,f2432])).

fof(f168,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X1,X0)
        | X0 = X1
        | ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f205,plain,
    ( spl4_11
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f403,plain,
    ( spl4_25
  <=> k5_lattices(sK0) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f2442,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ r3_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | ~ m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f2424,f206])).

fof(f206,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f205])).

fof(f2424,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ r3_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | ~ m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl4_7
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(resolution,[],[f2418,f169])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f168])).

fof(f2418,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0))
    | ~ spl4_24
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f2407,f400])).

fof(f2407,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_25 ),
    inference(superposition,[],[f2393,f405])).

fof(f405,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f403])).

fof(f2393,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,sK2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f2388,f63])).

fof(f63,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f2388,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,sK2,X0)) ) ),
    inference(resolution,[],[f2375,f64])).

fof(f64,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f2375,plain,(
    ! [X39,X38] :
      ( ~ r3_lattices(sK0,sK1,X39)
      | ~ m1_subset_1(X39,u1_struct_0(sK0))
      | ~ m1_subset_1(X38,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,sK1,X38),k4_lattices(sK0,X39,X38)) ) ),
    inference(resolution,[],[f1147,f62])).

fof(f1147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X2,X1),k4_lattices(sK0,X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f1146])).

fof(f1146,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(sK0,k2_lattices(sK0,X2,X1),k4_lattices(sK0,X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f968,f105])).

fof(f968,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(sK0,k2_lattices(sK0,X1,X2),k2_lattices(sK0,X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f967])).

fof(f967,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X1,X2),k2_lattices(sK0,X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f605,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f154,f58])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f153,f61])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f152,f59])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f151,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f150,f78])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f91,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f605,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(sK0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X2,X0),k2_lattices(sK0,X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f604,f58])).

fof(f604,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X2,X0),k2_lattices(sK0,X1,X0))
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X2,X1) ) ),
    inference(subsumption_resolution,[],[f603,f61])).

fof(f603,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,k2_lattices(sK0,X2,X0),k2_lattices(sK0,X1,X0))
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X2,X1) ) ),
    inference(resolution,[],[f386,f59])).

fof(f386,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f385,f81])).

fof(f385,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f384,f80])).

fof(f384,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f383])).

fof(f383,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f83,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).

fof(f429,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | spl4_24 ),
    inference(subsumption_resolution,[],[f427,f58])).

fof(f427,plain,
    ( v2_struct_0(sK0)
    | spl4_24 ),
    inference(subsumption_resolution,[],[f426,f61])).

fof(f426,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_24 ),
    inference(subsumption_resolution,[],[f425,f63])).

fof(f425,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_24 ),
    inference(resolution,[],[f401,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f401,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f399])).

fof(f424,plain,
    ( ~ spl4_24
    | spl4_25
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f423,f252,f128,f403,f399])).

fof(f252,plain,
    ( spl4_15
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X1),X1)
        | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f423,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f392,f63])).

fof(f392,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(superposition,[],[f129,f272])).

fof(f272,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ spl4_15 ),
    inference(resolution,[],[f270,f63])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X0),X0) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f269,f58])).

fof(f269,plain,
    ( ! [X0] :
        ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f268,f61])).

fof(f268,plain,
    ( ! [X0] :
        ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_15 ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,
    ( ! [X0] :
        ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_15 ),
    inference(resolution,[],[f253,f88])).

fof(f253,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
        | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f252])).

fof(f363,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f361,f61])).

fof(f361,plain,
    ( ~ l3_lattices(sK0)
    | spl4_10 ),
    inference(subsumption_resolution,[],[f360,f58])).

fof(f360,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_10 ),
    inference(subsumption_resolution,[],[f359,f60])).

fof(f359,plain,
    ( ~ v17_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_10 ),
    inference(resolution,[],[f358,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

fof(f358,plain,
    ( ~ v15_lattices(sK0)
    | spl4_10 ),
    inference(subsumption_resolution,[],[f357,f61])).

fof(f357,plain,
    ( ~ v15_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl4_10 ),
    inference(subsumption_resolution,[],[f356,f58])).

fof(f356,plain,
    ( ~ v15_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_10 ),
    inference(resolution,[],[f203,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).

fof(f203,plain,
    ( ~ v13_lattices(sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f201])).

fof(f341,plain,
    ( ~ spl4_2
    | spl4_11
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl4_2
    | spl4_11
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f324,f298])).

fof(f298,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl4_16
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f324,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl4_2
    | spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f323,f62])).

fof(f323,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_2
    | spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f291,f207])).

fof(f207,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f205])).

fof(f291,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(superposition,[],[f115,f271])).

fof(f271,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ spl4_15 ),
    inference(resolution,[],[f270,f62])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_2
  <=> ! [X1,X0] :
        ( m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f334,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f332,f58])).

fof(f332,plain,
    ( v2_struct_0(sK0)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f331,f61])).

fof(f331,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_16 ),
    inference(subsumption_resolution,[],[f330,f62])).

fof(f330,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_16 ),
    inference(resolution,[],[f299,f88])).

fof(f299,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f297])).

fof(f264,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f262,f61])).

fof(f262,plain,
    ( ~ l3_lattices(sK0)
    | spl4_14 ),
    inference(subsumption_resolution,[],[f261,f58])).

fof(f261,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_14 ),
    inference(subsumption_resolution,[],[f260,f59])).

fof(f260,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_14 ),
    inference(resolution,[],[f250,f81])).

fof(f250,plain,
    ( ~ v9_lattices(sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl4_14
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f259,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f257,f61])).

fof(f257,plain,
    ( ~ l3_lattices(sK0)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f256,f58])).

fof(f256,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f255,f59])).

fof(f255,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_13 ),
    inference(resolution,[],[f246,f80])).

fof(f246,plain,
    ( ~ v8_lattices(sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl4_13
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f254,plain,
    ( ~ spl4_13
    | ~ spl4_14
    | spl4_15
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f242,f124,f252,f248,f244])).

fof(f124,plain,
    ( spl4_3
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f242,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
        | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X1),X1)
        | ~ v9_lattices(sK0)
        | ~ v8_lattices(sK0) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f241,f58])).

fof(f241,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
        | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X1),X1)
        | ~ v9_lattices(sK0)
        | ~ v8_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f240,f125])).

fof(f125,plain,
    ( v6_lattices(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f240,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X1),X1)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f239,f61])).

fof(f239,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X1),X1)
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f238])).

fof(f238,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,X1),X1)
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f236,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(condensation,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,X0,X1) = k5_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f235,f58])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,X0,X1) = k5_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f234,f59])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,X0,X1) = k5_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f61])).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k4_lattices(sK0,X0,X1) = k5_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f60])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k4_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f178,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f176,f61])).

fof(f176,plain,
    ( ~ l3_lattices(sK0)
    | spl4_6 ),
    inference(resolution,[],[f166,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f166,plain,
    ( ~ l2_lattices(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_6
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f175,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f173,f61])).

fof(f173,plain,
    ( ~ l3_lattices(sK0)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f172,f58])).

fof(f172,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_5 ),
    inference(subsumption_resolution,[],[f171,f59])).

fof(f171,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_5 ),
    inference(resolution,[],[f162,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f162,plain,
    ( ~ v4_lattices(sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_5
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f170,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f158,f168,f164,f160])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f157,f58])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f155,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(f135,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f133,f61])).

fof(f133,plain,
    ( ~ l3_lattices(sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f132,f58])).

fof(f132,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f131,f59])).

fof(f131,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_3 ),
    inference(resolution,[],[f126,f78])).

fof(f126,plain,
    ( ~ v6_lattices(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f130,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f122,f110,f128,f124])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
        | ~ v6_lattices(sK0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f120,f58])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f111,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f119,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f117,f61])).

fof(f117,plain,
    ( ~ l3_lattices(sK0)
    | spl4_1 ),
    inference(resolution,[],[f112,f66])).

fof(f112,plain,
    ( ~ l1_lattices(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f116,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f108,f114,f110])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f107,f58])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f89,f105])).

%------------------------------------------------------------------------------
