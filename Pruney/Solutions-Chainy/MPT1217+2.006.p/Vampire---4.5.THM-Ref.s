%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:45 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  282 (1039 expanded)
%              Number of leaves         :   39 ( 377 expanded)
%              Depth                    :   24
%              Number of atoms          : 1429 (7173 expanded)
%              Number of equality atoms :  107 ( 120 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2352,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f144,f159,f162,f281,f299,f419,f424,f482,f487,f752,f756,f787,f1310,f2248,f2257,f2286,f2351])).

fof(f2351,plain,
    ( ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f2350])).

fof(f2350,plain,
    ( $false
    | ~ spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f2308,f398])).

fof(f398,plain,
    ( r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl7_17
  <=> r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f2308,plain,
    ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f2307,f406])).

fof(f406,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl7_19
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f2307,plain,
    ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_18
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f841,f402])).

fof(f402,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl7_18
  <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f841,plain,
    ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl7_35 ),
    inference(resolution,[],[f751,f73])).

fof(f73,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f51,f50,f49])).

fof(f49,plain,
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

fof(f50,plain,
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

fof(f51,plain,
    ( ? [X2] :
        ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1))
        & r3_lattices(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
      & r3_lattices(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f751,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,X0,X1)
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f750])).

fof(f750,plain,
    ( spl7_35
  <=> ! [X1,X0] :
        ( ~ r1_lattices(sK0,X0,X1)
        | r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f2286,plain,
    ( ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22
    | ~ spl7_90 ),
    inference(avatar_contradiction_clause,[],[f2285])).

fof(f2285,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22
    | ~ spl7_90 ),
    inference(trivial_inequality_removal,[],[f2266])).

fof(f2266,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,sK1)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22
    | ~ spl7_90 ),
    inference(backward_demodulation,[],[f1342,f2247])).

fof(f2247,plain,
    ( sK1 = k2_lattices(sK0,sK2,sK1)
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f2245])).

fof(f2245,plain,
    ( spl7_90
  <=> sK1 = k2_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f1342,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1341,f66])).

fof(f66,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f1341,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_11
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1340,f271])).

fof(f271,plain,
    ( v6_lattices(sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl7_11
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1340,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1))
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_4
    | ~ spl7_6
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1339,f154])).

fof(f154,plain,
    ( l1_lattices(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl7_6
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1339,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_4
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1338,f71])).

fof(f71,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f1338,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_4
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1337,f70])).

fof(f70,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f1337,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_4
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(superposition,[],[f1190,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f1190,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1))
    | ~ spl7_4
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1189,f66])).

fof(f1189,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | ~ spl7_4
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1188,f136])).

fof(f136,plain,
    ( l2_lattices(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_4
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1188,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1187,f402])).

fof(f1187,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1186,f406])).

fof(f1186,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1154,f399])).

fof(f399,plain,
    ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f397])).

fof(f1154,plain,
    ( k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1))
    | r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(superposition,[],[f87,f502])).

fof(f502,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK2,sK1))
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f498,f70])).

fof(f498,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(resolution,[],[f493,f406])).

fof(f493,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0)) = k7_lattices(sK0,k4_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_18
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f489,f71])).

fof(f489,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0)) = k7_lattices(sK0,k4_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl7_18
    | ~ spl7_22 ),
    inference(resolution,[],[f478,f402])).

fof(f478,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0))
        | k1_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X3)) = k7_lattices(sK0,k4_lattices(sK0,X2,X3))
        | ~ m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl7_22
  <=> ! [X3,X2] :
        ( k1_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X3)) = k7_lattices(sK0,k4_lattices(sK0,X2,X3))
        | ~ m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f2257,plain,
    ( ~ spl7_7
    | spl7_89 ),
    inference(avatar_contradiction_clause,[],[f2256])).

fof(f2256,plain,
    ( $false
    | ~ spl7_7
    | spl7_89 ),
    inference(subsumption_resolution,[],[f2255,f71])).

fof(f2255,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_7
    | spl7_89 ),
    inference(subsumption_resolution,[],[f2253,f70])).

fof(f2253,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_7
    | spl7_89 ),
    inference(resolution,[],[f2243,f158])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_7
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f2243,plain,
    ( ~ r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1)
    | spl7_89 ),
    inference(avatar_component_clause,[],[f2241])).

fof(f2241,plain,
    ( spl7_89
  <=> r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f2248,plain,
    ( ~ spl7_89
    | spl7_90
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f2239,f1293,f274,f135,f2245,f2241])).

fof(f274,plain,
    ( spl7_12
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1293,plain,
    ( spl7_49
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f2239,plain,
    ( sK1 = k2_lattices(sK0,sK2,sK1)
    | ~ r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1)
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_49 ),
    inference(subsumption_resolution,[],[f2238,f70])).

fof(f2238,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK2,sK1)
    | ~ r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1)
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_49 ),
    inference(subsumption_resolution,[],[f2229,f1294])).

fof(f1294,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f1293])).

fof(f2229,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK2,sK1)
    | ~ r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1)
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(resolution,[],[f2221,f228])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f227,f69])).

fof(f69,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | X0 = X1
      | ~ r1_lattices(sK0,X1,X0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f226,f66])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | X0 = X1
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f225,f67])).

fof(f67,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ r1_lattices(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | X1 = X2
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f224,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | X1 = X2
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | X1 = X2
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f85,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X0)
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | X1 = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f2221,plain,
    ( r1_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK1))
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f2213,f70])).

fof(f2213,plain,
    ( r1_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(superposition,[],[f2206,f994])).

fof(f994,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(resolution,[],[f986,f70])).

fof(f986,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,X4,X4) = X4 )
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(duplicate_literal_removal,[],[f982])).

fof(f982,plain,
    ( ! [X4] :
        ( k2_lattices(sK0,X4,X4) = X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(superposition,[],[f167,f828])).

fof(f828,plain,
    ( ! [X3] :
        ( k1_lattices(sK0,X3,X3) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f827,f66])).

fof(f827,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X3,X3) = X3
        | v2_struct_0(sK0) )
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f823,f136])).

fof(f823,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X3,X3) = X3
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_12 ),
    inference(duplicate_literal_removal,[],[f822])).

fof(f822,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X3,X3) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_12 ),
    inference(resolution,[],[f275,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f275,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f274])).

fof(f167,plain,(
    ! [X0,X1] :
      ( k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f166,f66])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f165,f69])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f109,f67])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f94,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0)))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0)))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f2206,plain,(
    ! [X11] :
      ( r1_lattices(sK0,k2_lattices(sK0,sK1,X11),k2_lattices(sK0,sK2,X11))
      | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f2205,f70])).

fof(f2205,plain,(
    ! [X11] :
      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,sK1,X11),k2_lattices(sK0,sK2,X11))
      | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f2193,f71])).

fof(f2193,plain,(
    ! [X11] :
      ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,sK1,X11),k2_lattices(sK0,sK2,X11))
      | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1430,f264])).

fof(f264,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f263,f71])).

fof(f263,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f260,f70])).

fof(f260,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f259,f72])).

fof(f72,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f258,f66])).

fof(f258,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f257,f69])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f256,f67])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f255,f82])).

fof(f255,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f254,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f254,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f103,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f1430,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(sK0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X2,X0),k2_lattices(sK0,X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1429,f66])).

fof(f1429,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X2,X0),k2_lattices(sK0,X1,X0))
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X2,X1) ) ),
    inference(subsumption_resolution,[],[f1428,f69])).

fof(f1428,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,k2_lattices(sK0,X2,X0),k2_lattices(sK0,X1,X0))
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X2,X1) ) ),
    inference(resolution,[],[f566,f67])).

fof(f566,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f565,f82])).

fof(f565,plain,(
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
    inference(subsumption_resolution,[],[f564,f81])).

fof(f564,plain,(
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
    inference(duplicate_literal_removal,[],[f563])).

fof(f563,plain,(
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
    inference(resolution,[],[f83,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f1310,plain,
    ( ~ spl7_6
    | spl7_49 ),
    inference(avatar_contradiction_clause,[],[f1309])).

fof(f1309,plain,
    ( $false
    | ~ spl7_6
    | spl7_49 ),
    inference(subsumption_resolution,[],[f1308,f66])).

fof(f1308,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_6
    | spl7_49 ),
    inference(subsumption_resolution,[],[f1307,f154])).

fof(f1307,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_49 ),
    inference(subsumption_resolution,[],[f1306,f71])).

fof(f1306,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_49 ),
    inference(subsumption_resolution,[],[f1305,f70])).

fof(f1305,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_49 ),
    inference(resolution,[],[f1295,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f1295,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl7_49 ),
    inference(avatar_component_clause,[],[f1293])).

fof(f787,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f785,f69])).

fof(f785,plain,
    ( ~ l3_lattices(sK0)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f784,f66])).

fof(f784,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f783,f67])).

fof(f783,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_3 ),
    inference(resolution,[],[f130,f81])).

fof(f130,plain,
    ( ~ v8_lattices(sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_3
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f756,plain,
    ( ~ spl7_3
    | spl7_12
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f755,f270,f191,f274,f129])).

fof(f191,plain,
    ( spl7_10
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f755,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,X0)
        | ~ v8_lattices(sK0) )
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f754,f66])).

fof(f754,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,X0)
        | ~ v8_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f753,f271])).

fof(f753,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,X0)
        | ~ v8_lattices(sK0)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f265,f193])).

fof(f193,plain,
    ( v9_lattices(sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f265,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f262,f69])).

fof(f262,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X0)
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f259,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(condensation,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
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
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(f752,plain,
    ( ~ spl7_3
    | spl7_35
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f748,f270,f191,f750,f129])).

fof(f748,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v8_lattices(sK0)
        | r3_lattices(sK0,X0,X1) )
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f383,f271])).

fof(f383,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v8_lattices(sK0)
        | ~ v6_lattices(sK0)
        | r3_lattices(sK0,X0,X1) )
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f382,f193])).

fof(f382,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | r3_lattices(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f381,f69])).

fof(f381,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | r3_lattices(sK0,X0,X1) ) ),
    inference(resolution,[],[f104,f66])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f487,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | spl7_21 ),
    inference(subsumption_resolution,[],[f485,f69])).

fof(f485,plain,
    ( ~ l3_lattices(sK0)
    | spl7_21 ),
    inference(subsumption_resolution,[],[f484,f66])).

fof(f484,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_21 ),
    inference(subsumption_resolution,[],[f483,f67])).

fof(f483,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_21 ),
    inference(resolution,[],[f475,f77])).

fof(f475,plain,
    ( ~ v4_lattices(sK0)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f473])).

fof(f473,plain,
    ( spl7_21
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f482,plain,
    ( ~ spl7_21
    | spl7_22
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f481,f135,f477,f473])).

fof(f481,plain,
    ( ! [X0,X1] :
        ( k7_lattices(sK0,k4_lattices(sK0,X0,X1)) = k1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
        | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ v4_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f480,f66])).

fof(f480,plain,
    ( ! [X0,X1] :
        ( k7_lattices(sK0,k4_lattices(sK0,X0,X1)) = k1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
        | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ v4_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f469,f136])).

fof(f469,plain,(
    ! [X0,X1] :
      ( k7_lattices(sK0,k4_lattices(sK0,X0,X1)) = k1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f99,f467])).

fof(f467,plain,(
    ! [X0,X1] :
      ( k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f466,f66])).

fof(f466,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f465,f67])).

fof(f465,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f464,f69])).

fof(f464,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f84,f68])).

fof(f68,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattices)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f424,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | spl7_19 ),
    inference(subsumption_resolution,[],[f422,f66])).

fof(f422,plain,
    ( v2_struct_0(sK0)
    | spl7_19 ),
    inference(subsumption_resolution,[],[f421,f69])).

fof(f421,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_19 ),
    inference(subsumption_resolution,[],[f420,f70])).

fof(f420,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_19 ),
    inference(resolution,[],[f407,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f407,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | spl7_19 ),
    inference(avatar_component_clause,[],[f405])).

fof(f419,plain,(
    spl7_18 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | spl7_18 ),
    inference(subsumption_resolution,[],[f417,f66])).

fof(f417,plain,
    ( v2_struct_0(sK0)
    | spl7_18 ),
    inference(subsumption_resolution,[],[f416,f69])).

fof(f416,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_18 ),
    inference(subsumption_resolution,[],[f415,f71])).

fof(f415,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_18 ),
    inference(resolution,[],[f403,f98])).

fof(f403,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f401])).

fof(f299,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl7_10 ),
    inference(subsumption_resolution,[],[f297,f69])).

fof(f297,plain,
    ( ~ l3_lattices(sK0)
    | spl7_10 ),
    inference(subsumption_resolution,[],[f296,f66])).

fof(f296,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_10 ),
    inference(subsumption_resolution,[],[f295,f67])).

fof(f295,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_10 ),
    inference(resolution,[],[f192,f82])).

fof(f192,plain,
    ( ~ v9_lattices(sK0)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f281,plain,(
    spl7_11 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl7_11 ),
    inference(subsumption_resolution,[],[f279,f69])).

fof(f279,plain,
    ( ~ l3_lattices(sK0)
    | spl7_11 ),
    inference(subsumption_resolution,[],[f278,f66])).

fof(f278,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_11 ),
    inference(subsumption_resolution,[],[f277,f67])).

fof(f277,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_11 ),
    inference(resolution,[],[f272,f79])).

fof(f272,plain,
    ( ~ v6_lattices(sK0)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f270])).

fof(f162,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f160,f69])).

fof(f160,plain,
    ( ~ l3_lattices(sK0)
    | spl7_6 ),
    inference(resolution,[],[f155,f74])).

fof(f74,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f155,plain,
    ( ~ l1_lattices(sK0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f159,plain,
    ( ~ spl7_6
    | spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f151,f139,f157,f153])).

fof(f139,plain,
    ( spl7_5
  <=> ! [X1,X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_lattices(sK0) )
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f150,f66])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f140,f100])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f144,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f142,f69])).

fof(f142,plain,
    ( ~ l3_lattices(sK0)
    | spl7_4 ),
    inference(resolution,[],[f137,f75])).

fof(f137,plain,
    ( ~ l2_lattices(sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f141,plain,
    ( ~ spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f133,f139,f135])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f116,f66])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( X1 != X1
      | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( X1 != X1
      | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f87,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f111,f66])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f110,f69])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f107,f67])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f90,f81])).

fof(f90,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:57:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.22/0.52  % (30107)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.52  % (30109)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.53  % (30112)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.53  % (30108)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.54  % (30116)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.54  % (30110)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.54  % (30111)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.54  % (30114)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.54  % (30122)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.54  % (30129)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.54  % (30128)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.55  % (30121)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.55  % (30132)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.55  % (30133)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.55  % (30120)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.55  % (30123)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.55  % (30131)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.55  % (30113)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.55  % (30124)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.55  % (30136)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.55  % (30125)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.56  % (30135)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.56  % (30124)Refutation not found, incomplete strategy% (30124)------------------------------
% 1.37/0.56  % (30124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (30124)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (30124)Memory used [KB]: 10618
% 1.37/0.56  % (30124)Time elapsed: 0.148 s
% 1.37/0.56  % (30124)------------------------------
% 1.37/0.56  % (30124)------------------------------
% 1.37/0.56  % (30115)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.56  % (30129)Refutation not found, incomplete strategy% (30129)------------------------------
% 1.37/0.56  % (30129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (30129)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (30129)Memory used [KB]: 10874
% 1.37/0.56  % (30129)Time elapsed: 0.108 s
% 1.37/0.56  % (30129)------------------------------
% 1.37/0.56  % (30129)------------------------------
% 1.37/0.56  % (30127)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.56  % (30117)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.56  % (30130)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.56  % (30118)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.58  % (30119)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.59  % (30134)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.60  % (30126)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.11/0.67  % (30110)Refutation found. Thanks to Tanya!
% 2.11/0.67  % SZS status Theorem for theBenchmark
% 2.11/0.67  % SZS output start Proof for theBenchmark
% 2.11/0.67  fof(f2352,plain,(
% 2.11/0.67    $false),
% 2.11/0.67    inference(avatar_sat_refutation,[],[f141,f144,f159,f162,f281,f299,f419,f424,f482,f487,f752,f756,f787,f1310,f2248,f2257,f2286,f2351])).
% 2.11/0.67  fof(f2351,plain,(
% 2.11/0.67    ~spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_35),
% 2.11/0.67    inference(avatar_contradiction_clause,[],[f2350])).
% 2.11/0.67  fof(f2350,plain,(
% 2.11/0.67    $false | (~spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_35)),
% 2.11/0.67    inference(subsumption_resolution,[],[f2308,f398])).
% 2.11/0.67  fof(f398,plain,(
% 2.11/0.67    r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~spl7_17),
% 2.11/0.67    inference(avatar_component_clause,[],[f397])).
% 2.11/0.67  fof(f397,plain,(
% 2.11/0.67    spl7_17 <=> r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.11/0.67  fof(f2308,plain,(
% 2.11/0.67    ~r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | (~spl7_18 | ~spl7_19 | ~spl7_35)),
% 2.11/0.67    inference(subsumption_resolution,[],[f2307,f406])).
% 2.11/0.67  fof(f406,plain,(
% 2.11/0.67    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~spl7_19),
% 2.11/0.67    inference(avatar_component_clause,[],[f405])).
% 2.11/0.67  fof(f405,plain,(
% 2.11/0.67    spl7_19 <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 2.11/0.67  fof(f2307,plain,(
% 2.11/0.67    ~r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | (~spl7_18 | ~spl7_35)),
% 2.11/0.67    inference(subsumption_resolution,[],[f841,f402])).
% 2.11/0.67  fof(f402,plain,(
% 2.11/0.67    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~spl7_18),
% 2.11/0.67    inference(avatar_component_clause,[],[f401])).
% 2.11/0.67  fof(f401,plain,(
% 2.11/0.67    spl7_18 <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.11/0.67  fof(f841,plain,(
% 2.11/0.67    ~r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~spl7_35),
% 2.11/0.67    inference(resolution,[],[f751,f73])).
% 2.11/0.67  fof(f73,plain,(
% 2.11/0.67    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 2.11/0.67    inference(cnf_transformation,[],[f52])).
% 2.11/0.67  fof(f52,plain,(
% 2.11/0.67    ((~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f51,f50,f49])).
% 2.11/0.67  fof(f49,plain,(
% 2.11/0.67    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f50,plain,(
% 2.11/0.67    ? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f51,plain,(
% 2.11/0.67    ? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f19,plain,(
% 2.11/0.67    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.11/0.67    inference(flattening,[],[f18])).
% 2.11/0.67  fof(f18,plain,(
% 2.11/0.67    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.11/0.67    inference(ennf_transformation,[],[f17])).
% 2.11/0.67  fof(f17,negated_conjecture,(
% 2.11/0.67    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 2.11/0.67    inference(negated_conjecture,[],[f16])).
% 2.11/0.67  fof(f16,conjecture,(
% 2.11/0.67    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 2.11/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).
% 2.11/0.67  fof(f751,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r3_lattices(sK0,X0,X1) | ~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_35),
% 2.11/0.67    inference(avatar_component_clause,[],[f750])).
% 2.11/0.67  fof(f750,plain,(
% 2.11/0.67    spl7_35 <=> ! [X1,X0] : (~r1_lattices(sK0,X0,X1) | r3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 2.11/0.67  fof(f2286,plain,(
% 2.11/0.67    ~spl7_4 | ~spl7_6 | ~spl7_11 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22 | ~spl7_90),
% 2.11/0.67    inference(avatar_contradiction_clause,[],[f2285])).
% 2.11/0.67  fof(f2285,plain,(
% 2.11/0.67    $false | (~spl7_4 | ~spl7_6 | ~spl7_11 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22 | ~spl7_90)),
% 2.11/0.67    inference(trivial_inequality_removal,[],[f2266])).
% 2.11/0.67  fof(f2266,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,sK1) | (~spl7_4 | ~spl7_6 | ~spl7_11 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22 | ~spl7_90)),
% 2.11/0.67    inference(backward_demodulation,[],[f1342,f2247])).
% 2.11/0.67  fof(f2247,plain,(
% 2.11/0.67    sK1 = k2_lattices(sK0,sK2,sK1) | ~spl7_90),
% 2.11/0.67    inference(avatar_component_clause,[],[f2245])).
% 2.11/0.67  fof(f2245,plain,(
% 2.11/0.67    spl7_90 <=> sK1 = k2_lattices(sK0,sK2,sK1)),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).
% 2.11/0.67  fof(f1342,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1)) | (~spl7_4 | ~spl7_6 | ~spl7_11 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1341,f66])).
% 2.11/0.67  fof(f66,plain,(
% 2.11/0.67    ~v2_struct_0(sK0)),
% 2.11/0.67    inference(cnf_transformation,[],[f52])).
% 2.11/0.67  fof(f1341,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1)) | v2_struct_0(sK0) | (~spl7_4 | ~spl7_6 | ~spl7_11 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1340,f271])).
% 2.11/0.67  fof(f271,plain,(
% 2.11/0.67    v6_lattices(sK0) | ~spl7_11),
% 2.11/0.67    inference(avatar_component_clause,[],[f270])).
% 2.11/0.67  fof(f270,plain,(
% 2.11/0.67    spl7_11 <=> v6_lattices(sK0)),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 2.11/0.67  fof(f1340,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1)) | ~v6_lattices(sK0) | v2_struct_0(sK0) | (~spl7_4 | ~spl7_6 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1339,f154])).
% 2.11/0.67  fof(f154,plain,(
% 2.11/0.67    l1_lattices(sK0) | ~spl7_6),
% 2.11/0.67    inference(avatar_component_clause,[],[f153])).
% 2.11/0.67  fof(f153,plain,(
% 2.11/0.67    spl7_6 <=> l1_lattices(sK0)),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.11/0.67  fof(f1339,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | (~spl7_4 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1338,f71])).
% 2.11/0.67  fof(f71,plain,(
% 2.11/0.67    m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.11/0.67    inference(cnf_transformation,[],[f52])).
% 2.11/0.67  fof(f1338,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | (~spl7_4 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1337,f70])).
% 2.11/0.67  fof(f70,plain,(
% 2.11/0.67    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.11/0.67    inference(cnf_transformation,[],[f52])).
% 2.11/0.67  fof(f1337,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k2_lattices(sK0,sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | (~spl7_4 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(superposition,[],[f1190,f101])).
% 2.11/0.67  fof(f101,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f44])).
% 2.11/0.67  fof(f44,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.67    inference(flattening,[],[f43])).
% 2.11/0.67  fof(f43,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.67    inference(ennf_transformation,[],[f9])).
% 2.11/0.67  fof(f9,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 2.11/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 2.11/0.67  fof(f1190,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) | (~spl7_4 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1189,f66])).
% 2.11/0.67  fof(f1189,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) | v2_struct_0(sK0) | (~spl7_4 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1188,f136])).
% 2.11/0.67  fof(f136,plain,(
% 2.11/0.67    l2_lattices(sK0) | ~spl7_4),
% 2.11/0.67    inference(avatar_component_clause,[],[f135])).
% 2.11/0.67  fof(f135,plain,(
% 2.11/0.67    spl7_4 <=> l2_lattices(sK0)),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.11/0.67  fof(f1188,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | (spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1187,f402])).
% 2.11/0.67  fof(f1187,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | (spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1186,f406])).
% 2.11/0.67  fof(f1186,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | (spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f1154,f399])).
% 2.11/0.67  fof(f399,plain,(
% 2.11/0.67    ~r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | spl7_17),
% 2.11/0.67    inference(avatar_component_clause,[],[f397])).
% 2.11/0.67  fof(f1154,plain,(
% 2.11/0.67    k7_lattices(sK0,sK1) != k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) | r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | (~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(superposition,[],[f87,f502])).
% 2.11/0.67  fof(f502,plain,(
% 2.11/0.67    k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) | (~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f498,f70])).
% 2.11/0.67  fof(f498,plain,(
% 2.11/0.67    k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl7_18 | ~spl7_19 | ~spl7_22)),
% 2.11/0.67    inference(resolution,[],[f493,f406])).
% 2.11/0.67  fof(f493,plain,(
% 2.11/0.67    ( ! [X0] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0)) = k7_lattices(sK0,k4_lattices(sK0,sK2,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_18 | ~spl7_22)),
% 2.11/0.67    inference(subsumption_resolution,[],[f489,f71])).
% 2.11/0.67  fof(f489,plain,(
% 2.11/0.67    ( ! [X0] : (k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0)) = k7_lattices(sK0,k4_lattices(sK0,sK2,X0)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0))) ) | (~spl7_18 | ~spl7_22)),
% 2.11/0.67    inference(resolution,[],[f478,f402])).
% 2.11/0.67  fof(f478,plain,(
% 2.11/0.67    ( ! [X2,X3] : (~m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0)) | k1_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X3)) = k7_lattices(sK0,k4_lattices(sK0,X2,X3)) | ~m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl7_22),
% 2.11/0.67    inference(avatar_component_clause,[],[f477])).
% 2.11/0.67  fof(f477,plain,(
% 2.11/0.67    spl7_22 <=> ! [X3,X2] : (k1_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X3)) = k7_lattices(sK0,k4_lattices(sK0,X2,X3)) | ~m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 2.11/0.67  fof(f87,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f53])).
% 2.11/0.67  fof(f53,plain,(
% 2.11/0.67    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.67    inference(nnf_transformation,[],[f30])).
% 2.11/0.67  fof(f30,plain,(
% 2.11/0.67    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.67    inference(flattening,[],[f29])).
% 2.11/0.67  fof(f29,plain,(
% 2.11/0.67    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.67    inference(ennf_transformation,[],[f2])).
% 2.11/0.67  fof(f2,axiom,(
% 2.11/0.67    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 2.11/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 2.11/0.67  fof(f2257,plain,(
% 2.11/0.67    ~spl7_7 | spl7_89),
% 2.11/0.67    inference(avatar_contradiction_clause,[],[f2256])).
% 2.11/0.67  fof(f2256,plain,(
% 2.11/0.67    $false | (~spl7_7 | spl7_89)),
% 2.11/0.67    inference(subsumption_resolution,[],[f2255,f71])).
% 2.11/0.67  fof(f2255,plain,(
% 2.11/0.67    ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl7_7 | spl7_89)),
% 2.11/0.67    inference(subsumption_resolution,[],[f2253,f70])).
% 2.11/0.67  fof(f2253,plain,(
% 2.11/0.67    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl7_7 | spl7_89)),
% 2.11/0.67    inference(resolution,[],[f2243,f158])).
% 2.11/0.67  fof(f158,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_7),
% 2.11/0.67    inference(avatar_component_clause,[],[f157])).
% 2.11/0.67  fof(f157,plain,(
% 2.11/0.67    spl7_7 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.11/0.67  fof(f2243,plain,(
% 2.11/0.67    ~r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) | spl7_89),
% 2.11/0.67    inference(avatar_component_clause,[],[f2241])).
% 2.11/0.67  fof(f2241,plain,(
% 2.11/0.67    spl7_89 <=> r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1)),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).
% 2.11/0.67  fof(f2248,plain,(
% 2.11/0.67    ~spl7_89 | spl7_90 | ~spl7_4 | ~spl7_12 | ~spl7_49),
% 2.11/0.67    inference(avatar_split_clause,[],[f2239,f1293,f274,f135,f2245,f2241])).
% 2.11/0.67  fof(f274,plain,(
% 2.11/0.67    spl7_12 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X0))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.11/0.67  fof(f1293,plain,(
% 2.11/0.67    spl7_49 <=> m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))),
% 2.11/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 2.11/0.67  fof(f2239,plain,(
% 2.11/0.67    sK1 = k2_lattices(sK0,sK2,sK1) | ~r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) | (~spl7_4 | ~spl7_12 | ~spl7_49)),
% 2.11/0.67    inference(subsumption_resolution,[],[f2238,f70])).
% 2.11/0.67  fof(f2238,plain,(
% 2.11/0.67    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK2,sK1) | ~r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) | (~spl7_4 | ~spl7_12 | ~spl7_49)),
% 2.11/0.67    inference(subsumption_resolution,[],[f2229,f1294])).
% 2.11/0.67  fof(f1294,plain,(
% 2.11/0.67    m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) | ~spl7_49),
% 2.11/0.67    inference(avatar_component_clause,[],[f1293])).
% 2.11/0.67  fof(f2229,plain,(
% 2.11/0.67    ~m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK2,sK1) | ~r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) | (~spl7_4 | ~spl7_12)),
% 2.11/0.67    inference(resolution,[],[f2221,f228])).
% 2.11/0.67  fof(f228,plain,(
% 2.11/0.67    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1 | ~r1_lattices(sK0,X1,X0)) )),
% 2.11/0.67    inference(subsumption_resolution,[],[f227,f69])).
% 2.11/0.67  fof(f69,plain,(
% 2.11/0.67    l3_lattices(sK0)),
% 2.11/0.67    inference(cnf_transformation,[],[f52])).
% 2.11/0.67  fof(f227,plain,(
% 2.11/0.67    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1 | ~r1_lattices(sK0,X1,X0) | ~l3_lattices(sK0)) )),
% 2.11/0.67    inference(subsumption_resolution,[],[f226,f66])).
% 2.11/0.67  fof(f226,plain,(
% 2.11/0.67    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1 | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0) | ~l3_lattices(sK0)) )),
% 2.11/0.67    inference(resolution,[],[f225,f67])).
% 2.11/0.67  fof(f67,plain,(
% 2.11/0.67    v10_lattices(sK0)),
% 2.11/0.67    inference(cnf_transformation,[],[f52])).
% 2.11/0.67  fof(f225,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~r1_lattices(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 = X2 | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2) | ~l3_lattices(X0)) )),
% 2.11/0.67    inference(subsumption_resolution,[],[f224,f75])).
% 2.11/0.67  fof(f75,plain,(
% 2.11/0.67    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f20])).
% 2.11/0.67  fof(f20,plain,(
% 2.11/0.67    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 2.11/0.67    inference(ennf_transformation,[],[f7])).
% 2.11/0.67  fof(f7,axiom,(
% 2.11/0.67    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.11/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 2.11/0.67  fof(f224,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~r1_lattices(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l2_lattices(X0) | X1 = X2 | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 2.11/0.67    inference(duplicate_literal_removal,[],[f223])).
% 2.11/0.67  fof(f223,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~r1_lattices(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l2_lattices(X0) | X1 = X2 | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.11/0.67    inference(resolution,[],[f85,f77])).
% 2.11/0.67  fof(f77,plain,(
% 2.11/0.67    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f22])).
% 2.11/0.67  fof(f22,plain,(
% 2.11/0.67    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.11/0.67    inference(flattening,[],[f21])).
% 2.11/0.67  fof(f21,plain,(
% 2.11/0.67    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.11/0.67    inference(ennf_transformation,[],[f1])).
% 2.11/0.67  fof(f1,axiom,(
% 2.11/0.67    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.11/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 2.11/0.67  fof(f85,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~v4_lattices(X0) | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | X1 = X2 | v2_struct_0(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f28])).
% 2.11/0.67  fof(f28,plain,(
% 2.11/0.67    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.67    inference(flattening,[],[f27])).
% 2.11/0.67  fof(f27,plain,(
% 2.11/0.67    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.67    inference(ennf_transformation,[],[f13])).
% 2.11/0.67  fof(f13,axiom,(
% 2.11/0.67    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 2.11/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).
% 2.11/0.67  fof(f2221,plain,(
% 2.11/0.67    r1_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK1)) | (~spl7_4 | ~spl7_12)),
% 2.11/0.67    inference(subsumption_resolution,[],[f2213,f70])).
% 2.11/0.67  fof(f2213,plain,(
% 2.11/0.67    r1_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl7_4 | ~spl7_12)),
% 2.11/0.67    inference(superposition,[],[f2206,f994])).
% 2.11/0.67  fof(f994,plain,(
% 2.11/0.67    sK1 = k2_lattices(sK0,sK1,sK1) | (~spl7_4 | ~spl7_12)),
% 2.11/0.67    inference(resolution,[],[f986,f70])).
% 2.11/0.67  fof(f986,plain,(
% 2.11/0.67    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,X4,X4) = X4) ) | (~spl7_4 | ~spl7_12)),
% 2.11/0.67    inference(duplicate_literal_removal,[],[f982])).
% 2.11/0.67  fof(f982,plain,(
% 2.11/0.67    ( ! [X4] : (k2_lattices(sK0,X4,X4) = X4 | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (~spl7_4 | ~spl7_12)),
% 2.11/0.67    inference(superposition,[],[f167,f828])).
% 2.11/0.67  fof(f828,plain,(
% 2.11/0.67    ( ! [X3] : (k1_lattices(sK0,X3,X3) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl7_4 | ~spl7_12)),
% 2.11/0.67    inference(subsumption_resolution,[],[f827,f66])).
% 2.11/0.67  fof(f827,plain,(
% 2.11/0.67    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k1_lattices(sK0,X3,X3) = X3 | v2_struct_0(sK0)) ) | (~spl7_4 | ~spl7_12)),
% 2.11/0.67    inference(subsumption_resolution,[],[f823,f136])).
% 2.11/0.67  fof(f823,plain,(
% 2.11/0.67    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k1_lattices(sK0,X3,X3) = X3 | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_12),
% 2.11/0.67    inference(duplicate_literal_removal,[],[f822])).
% 2.11/0.67  fof(f822,plain,(
% 2.11/0.67    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k1_lattices(sK0,X3,X3) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_12),
% 2.11/0.67    inference(resolution,[],[f275,f86])).
% 2.11/0.67  fof(f86,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f53])).
% 2.11/0.67  fof(f275,plain,(
% 2.11/0.67    ( ! [X0] : (r1_lattices(sK0,X0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_12),
% 2.11/0.67    inference(avatar_component_clause,[],[f274])).
% 2.11/0.67  fof(f167,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.11/0.67    inference(subsumption_resolution,[],[f166,f66])).
% 2.11/0.67  fof(f166,plain,(
% 2.11/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0 | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.11/0.67    inference(subsumption_resolution,[],[f165,f69])).
% 2.11/0.67  fof(f165,plain,(
% 2.11/0.67    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0 | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.11/0.67    inference(resolution,[],[f109,f67])).
% 2.11/0.67  fof(f109,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 | ~l3_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 2.11/0.67    inference(duplicate_literal_removal,[],[f108])).
% 2.11/0.67  fof(f108,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 | ~l3_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 2.11/0.67    inference(resolution,[],[f94,f82])).
% 2.11/0.67  fof(f82,plain,(
% 2.11/0.67    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f22])).
% 2.11/0.67  fof(f94,plain,(
% 2.11/0.67    ( ! [X4,X0,X3] : (~v9_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f64])).
% 2.11/0.67  fof(f64,plain,(
% 2.11/0.67    ! [X0] : (((v9_lattices(X0) | ((sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f61,f63,f62])).
% 2.11/0.67  fof(f62,plain,(
% 2.11/0.67    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f63,plain,(
% 2.11/0.67    ! [X0] : (? [X2] : (sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f61,plain,(
% 2.11/0.67    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.67    inference(rectify,[],[f60])).
% 2.11/0.67  fof(f60,plain,(
% 2.11/0.67    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.67    inference(nnf_transformation,[],[f36])).
% 2.11/0.67  fof(f36,plain,(
% 2.11/0.67    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.67    inference(flattening,[],[f35])).
% 2.11/0.67  fof(f35,plain,(
% 2.11/0.67    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.67    inference(ennf_transformation,[],[f4])).
% 2.11/0.67  fof(f4,axiom,(
% 2.11/0.67    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 2.11/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 2.11/0.67  fof(f2206,plain,(
% 2.11/0.67    ( ! [X11] : (r1_lattices(sK0,k2_lattices(sK0,sK1,X11),k2_lattices(sK0,sK2,X11)) | ~m1_subset_1(X11,u1_struct_0(sK0))) )),
% 2.11/0.67    inference(subsumption_resolution,[],[f2205,f70])).
% 2.11/0.67  fof(f2205,plain,(
% 2.11/0.67    ( ! [X11] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,sK1,X11),k2_lattices(sK0,sK2,X11)) | ~m1_subset_1(X11,u1_struct_0(sK0))) )),
% 2.11/0.67    inference(subsumption_resolution,[],[f2193,f71])).
% 2.11/0.67  fof(f2193,plain,(
% 2.11/0.67    ( ! [X11] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,sK1,X11),k2_lattices(sK0,sK2,X11)) | ~m1_subset_1(X11,u1_struct_0(sK0))) )),
% 2.11/0.67    inference(resolution,[],[f1430,f264])).
% 2.11/0.67  fof(f264,plain,(
% 2.11/0.67    r1_lattices(sK0,sK1,sK2)),
% 2.11/0.67    inference(subsumption_resolution,[],[f263,f71])).
% 2.11/0.67  fof(f263,plain,(
% 2.11/0.67    r1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.11/0.67    inference(subsumption_resolution,[],[f260,f70])).
% 2.11/0.68  fof(f260,plain,(
% 2.11/0.68    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.11/0.68    inference(resolution,[],[f259,f72])).
% 2.11/0.68  fof(f72,plain,(
% 2.11/0.68    r3_lattices(sK0,sK1,sK2)),
% 2.11/0.68    inference(cnf_transformation,[],[f52])).
% 2.11/0.68  fof(f259,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~r3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f258,f66])).
% 2.11/0.68  fof(f258,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r3_lattices(sK0,X1,X0)) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f257,f69])).
% 2.11/0.68  fof(f257,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r3_lattices(sK0,X1,X0)) )),
% 2.11/0.68    inference(resolution,[],[f256,f67])).
% 2.11/0.68  fof(f256,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r3_lattices(X0,X1,X2)) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f255,f82])).
% 2.11/0.68  fof(f255,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f254,f81])).
% 2.11/0.68  fof(f81,plain,(
% 2.11/0.68    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f22])).
% 2.11/0.68  fof(f254,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 2.11/0.68    inference(duplicate_literal_removal,[],[f253])).
% 2.11/0.68  fof(f253,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.11/0.68    inference(resolution,[],[f103,f79])).
% 2.11/0.68  fof(f79,plain,(
% 2.11/0.68    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f22])).
% 2.11/0.68  fof(f103,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~v6_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f65])).
% 2.11/0.68  fof(f65,plain,(
% 2.11/0.68    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(nnf_transformation,[],[f48])).
% 2.11/0.68  fof(f48,plain,(
% 2.11/0.68    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(flattening,[],[f47])).
% 2.11/0.68  fof(f47,plain,(
% 2.11/0.68    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.68    inference(ennf_transformation,[],[f10])).
% 2.11/0.68  fof(f10,axiom,(
% 2.11/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 2.11/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 2.11/0.68  fof(f1430,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~r1_lattices(sK0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X2,X0),k2_lattices(sK0,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f1429,f66])).
% 2.11/0.68  fof(f1429,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X2,X0),k2_lattices(sK0,X1,X0)) | v2_struct_0(sK0) | ~r1_lattices(sK0,X2,X1)) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f1428,f69])).
% 2.11/0.68  fof(f1428,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,k2_lattices(sK0,X2,X0),k2_lattices(sK0,X1,X0)) | v2_struct_0(sK0) | ~r1_lattices(sK0,X2,X1)) )),
% 2.11/0.68    inference(resolution,[],[f566,f67])).
% 2.11/0.68  fof(f566,plain,(
% 2.11/0.68    ( ! [X2,X0,X3,X1] : (~v10_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f565,f82])).
% 2.11/0.68  fof(f565,plain,(
% 2.11/0.68    ( ! [X2,X0,X3,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f564,f81])).
% 2.11/0.68  fof(f564,plain,(
% 2.11/0.68    ( ! [X2,X0,X3,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 2.11/0.68    inference(duplicate_literal_removal,[],[f563])).
% 2.11/0.68  fof(f563,plain,(
% 2.11/0.68    ( ! [X2,X0,X3,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.11/0.68    inference(resolution,[],[f83,f80])).
% 2.11/0.68  fof(f80,plain,(
% 2.11/0.68    ( ! [X0] : (v7_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f22])).
% 2.11/0.68  fof(f83,plain,(
% 2.11/0.68    ( ! [X2,X0,X3,X1] : (~v7_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | v2_struct_0(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f24])).
% 2.11/0.68  fof(f24,plain,(
% 2.11/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(flattening,[],[f23])).
% 2.11/0.68  fof(f23,plain,(
% 2.11/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.68    inference(ennf_transformation,[],[f14])).
% 2.11/0.68  fof(f14,axiom,(
% 2.11/0.68    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 2.11/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).
% 2.11/0.68  fof(f1310,plain,(
% 2.11/0.68    ~spl7_6 | spl7_49),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f1309])).
% 2.11/0.68  fof(f1309,plain,(
% 2.11/0.68    $false | (~spl7_6 | spl7_49)),
% 2.11/0.68    inference(subsumption_resolution,[],[f1308,f66])).
% 2.11/0.68  fof(f1308,plain,(
% 2.11/0.68    v2_struct_0(sK0) | (~spl7_6 | spl7_49)),
% 2.11/0.68    inference(subsumption_resolution,[],[f1307,f154])).
% 2.11/0.68  fof(f1307,plain,(
% 2.11/0.68    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl7_49),
% 2.11/0.68    inference(subsumption_resolution,[],[f1306,f71])).
% 2.11/0.68  fof(f1306,plain,(
% 2.11/0.68    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl7_49),
% 2.11/0.68    inference(subsumption_resolution,[],[f1305,f70])).
% 2.11/0.68  fof(f1305,plain,(
% 2.11/0.68    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl7_49),
% 2.11/0.68    inference(resolution,[],[f1295,f100])).
% 2.11/0.68  fof(f100,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f42])).
% 2.11/0.68  fof(f42,plain,(
% 2.11/0.68    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(flattening,[],[f41])).
% 2.11/0.68  fof(f41,plain,(
% 2.11/0.68    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.68    inference(ennf_transformation,[],[f5])).
% 2.11/0.68  fof(f5,axiom,(
% 2.11/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 2.11/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).
% 2.11/0.68  fof(f1295,plain,(
% 2.11/0.68    ~m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) | spl7_49),
% 2.11/0.68    inference(avatar_component_clause,[],[f1293])).
% 2.11/0.68  fof(f787,plain,(
% 2.11/0.68    spl7_3),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f786])).
% 2.11/0.68  fof(f786,plain,(
% 2.11/0.68    $false | spl7_3),
% 2.11/0.68    inference(subsumption_resolution,[],[f785,f69])).
% 2.11/0.68  fof(f785,plain,(
% 2.11/0.68    ~l3_lattices(sK0) | spl7_3),
% 2.11/0.68    inference(subsumption_resolution,[],[f784,f66])).
% 2.11/0.68  fof(f784,plain,(
% 2.11/0.68    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_3),
% 2.11/0.68    inference(subsumption_resolution,[],[f783,f67])).
% 2.11/0.68  fof(f783,plain,(
% 2.11/0.68    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_3),
% 2.11/0.68    inference(resolution,[],[f130,f81])).
% 2.11/0.68  fof(f130,plain,(
% 2.11/0.68    ~v8_lattices(sK0) | spl7_3),
% 2.11/0.68    inference(avatar_component_clause,[],[f129])).
% 2.11/0.68  fof(f129,plain,(
% 2.11/0.68    spl7_3 <=> v8_lattices(sK0)),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.11/0.68  fof(f756,plain,(
% 2.11/0.68    ~spl7_3 | spl7_12 | ~spl7_10 | ~spl7_11),
% 2.11/0.68    inference(avatar_split_clause,[],[f755,f270,f191,f274,f129])).
% 2.11/0.68  fof(f191,plain,(
% 2.11/0.68    spl7_10 <=> v9_lattices(sK0)),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.11/0.68  fof(f755,plain,(
% 2.11/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X0) | ~v8_lattices(sK0)) ) | (~spl7_10 | ~spl7_11)),
% 2.11/0.68    inference(subsumption_resolution,[],[f754,f66])).
% 2.11/0.68  fof(f754,plain,(
% 2.11/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl7_10 | ~spl7_11)),
% 2.11/0.68    inference(subsumption_resolution,[],[f753,f271])).
% 2.11/0.68  fof(f753,plain,(
% 2.11/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_10),
% 2.11/0.68    inference(subsumption_resolution,[],[f265,f193])).
% 2.11/0.68  fof(f193,plain,(
% 2.11/0.68    v9_lattices(sK0) | ~spl7_10),
% 2.11/0.68    inference(avatar_component_clause,[],[f191])).
% 2.11/0.68  fof(f265,plain,(
% 2.11/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f262,f69])).
% 2.11/0.68  fof(f262,plain,(
% 2.11/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X0) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 2.11/0.68    inference(duplicate_literal_removal,[],[f261])).
% 2.11/0.68  fof(f261,plain,(
% 2.11/0.68    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 2.11/0.68    inference(resolution,[],[f259,f105])).
% 2.11/0.68  fof(f105,plain,(
% 2.11/0.68    ( ! [X0,X1] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.68    inference(condensation,[],[f102])).
% 2.11/0.68  fof(f102,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f46])).
% 2.11/0.68  fof(f46,plain,(
% 2.11/0.68    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(flattening,[],[f45])).
% 2.11/0.68  fof(f45,plain,(
% 2.11/0.68    ! [X0,X1,X2] : (r3_lattices(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.68    inference(ennf_transformation,[],[f11])).
% 2.11/0.68  fof(f11,axiom,(
% 2.11/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => r3_lattices(X0,X1,X1))),
% 2.11/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).
% 2.11/0.68  fof(f752,plain,(
% 2.11/0.68    ~spl7_3 | spl7_35 | ~spl7_10 | ~spl7_11),
% 2.11/0.68    inference(avatar_split_clause,[],[f748,f270,f191,f750,f129])).
% 2.11/0.68  fof(f748,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v8_lattices(sK0) | r3_lattices(sK0,X0,X1)) ) | (~spl7_10 | ~spl7_11)),
% 2.11/0.68    inference(subsumption_resolution,[],[f383,f271])).
% 2.11/0.68  fof(f383,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,X0,X1)) ) | ~spl7_10),
% 2.11/0.68    inference(subsumption_resolution,[],[f382,f193])).
% 2.11/0.68  fof(f382,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,X0,X1)) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f381,f69])).
% 2.11/0.68  fof(f381,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,X0,X1)) )),
% 2.11/0.68    inference(resolution,[],[f104,f66])).
% 2.11/0.68  fof(f104,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | r3_lattices(X0,X1,X2)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f65])).
% 2.11/0.68  fof(f487,plain,(
% 2.11/0.68    spl7_21),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f486])).
% 2.11/0.68  fof(f486,plain,(
% 2.11/0.68    $false | spl7_21),
% 2.11/0.68    inference(subsumption_resolution,[],[f485,f69])).
% 2.11/0.68  fof(f485,plain,(
% 2.11/0.68    ~l3_lattices(sK0) | spl7_21),
% 2.11/0.68    inference(subsumption_resolution,[],[f484,f66])).
% 2.11/0.68  fof(f484,plain,(
% 2.11/0.68    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_21),
% 2.11/0.68    inference(subsumption_resolution,[],[f483,f67])).
% 2.11/0.68  fof(f483,plain,(
% 2.11/0.68    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_21),
% 2.11/0.68    inference(resolution,[],[f475,f77])).
% 2.11/0.68  fof(f475,plain,(
% 2.11/0.68    ~v4_lattices(sK0) | spl7_21),
% 2.11/0.68    inference(avatar_component_clause,[],[f473])).
% 2.11/0.68  fof(f473,plain,(
% 2.11/0.68    spl7_21 <=> v4_lattices(sK0)),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 2.11/0.68  fof(f482,plain,(
% 2.11/0.68    ~spl7_21 | spl7_22 | ~spl7_4),
% 2.11/0.68    inference(avatar_split_clause,[],[f481,f135,f477,f473])).
% 2.11/0.68  fof(f481,plain,(
% 2.11/0.68    ( ! [X0,X1] : (k7_lattices(sK0,k4_lattices(sK0,X0,X1)) = k1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~v4_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_4),
% 2.11/0.68    inference(subsumption_resolution,[],[f480,f66])).
% 2.11/0.68  fof(f480,plain,(
% 2.11/0.68    ( ! [X0,X1] : (k7_lattices(sK0,k4_lattices(sK0,X0,X1)) = k1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~v4_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_4),
% 2.11/0.68    inference(subsumption_resolution,[],[f469,f136])).
% 2.11/0.68  fof(f469,plain,(
% 2.11/0.68    ( ! [X0,X1] : (k7_lattices(sK0,k4_lattices(sK0,X0,X1)) = k1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(superposition,[],[f99,f467])).
% 2.11/0.68  fof(f467,plain,(
% 2.11/0.68    ( ! [X0,X1] : (k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f466,f66])).
% 2.11/0.68  fof(f466,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | v2_struct_0(sK0)) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f465,f67])).
% 2.11/0.68  fof(f465,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f464,f69])).
% 2.11/0.68  fof(f464,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 2.11/0.68    inference(resolution,[],[f84,f68])).
% 2.11/0.68  fof(f68,plain,(
% 2.11/0.68    v17_lattices(sK0)),
% 2.11/0.68    inference(cnf_transformation,[],[f52])).
% 2.11/0.68  fof(f84,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~v17_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f26])).
% 2.11/0.68  fof(f26,plain,(
% 2.11/0.68    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(flattening,[],[f25])).
% 2.11/0.68  fof(f25,plain,(
% 2.11/0.68    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.68    inference(ennf_transformation,[],[f15])).
% 2.11/0.68  fof(f15,axiom,(
% 2.11/0.68    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 2.11/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattices)).
% 2.11/0.68  fof(f99,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f40])).
% 2.11/0.68  fof(f40,plain,(
% 2.11/0.68    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(flattening,[],[f39])).
% 2.11/0.68  fof(f39,plain,(
% 2.11/0.68    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.68    inference(ennf_transformation,[],[f8])).
% 2.11/0.68  fof(f8,axiom,(
% 2.11/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 2.11/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 2.11/0.68  fof(f424,plain,(
% 2.11/0.68    spl7_19),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f423])).
% 2.11/0.68  fof(f423,plain,(
% 2.11/0.68    $false | spl7_19),
% 2.11/0.68    inference(subsumption_resolution,[],[f422,f66])).
% 2.11/0.68  fof(f422,plain,(
% 2.11/0.68    v2_struct_0(sK0) | spl7_19),
% 2.11/0.68    inference(subsumption_resolution,[],[f421,f69])).
% 2.11/0.68  fof(f421,plain,(
% 2.11/0.68    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl7_19),
% 2.11/0.68    inference(subsumption_resolution,[],[f420,f70])).
% 2.11/0.68  fof(f420,plain,(
% 2.11/0.68    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl7_19),
% 2.11/0.68    inference(resolution,[],[f407,f98])).
% 2.11/0.68  fof(f98,plain,(
% 2.11/0.68    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f38])).
% 2.11/0.68  fof(f38,plain,(
% 2.11/0.68    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(flattening,[],[f37])).
% 2.11/0.68  fof(f37,plain,(
% 2.11/0.68    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.68    inference(ennf_transformation,[],[f6])).
% 2.11/0.68  fof(f6,axiom,(
% 2.11/0.68    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 2.11/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).
% 2.11/0.68  fof(f407,plain,(
% 2.11/0.68    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | spl7_19),
% 2.11/0.68    inference(avatar_component_clause,[],[f405])).
% 2.11/0.68  fof(f419,plain,(
% 2.11/0.68    spl7_18),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f418])).
% 2.11/0.68  fof(f418,plain,(
% 2.11/0.68    $false | spl7_18),
% 2.11/0.68    inference(subsumption_resolution,[],[f417,f66])).
% 2.11/0.68  fof(f417,plain,(
% 2.11/0.68    v2_struct_0(sK0) | spl7_18),
% 2.11/0.68    inference(subsumption_resolution,[],[f416,f69])).
% 2.11/0.68  fof(f416,plain,(
% 2.11/0.68    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl7_18),
% 2.11/0.68    inference(subsumption_resolution,[],[f415,f71])).
% 2.11/0.68  fof(f415,plain,(
% 2.11/0.68    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | spl7_18),
% 2.11/0.68    inference(resolution,[],[f403,f98])).
% 2.11/0.68  fof(f403,plain,(
% 2.11/0.68    ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | spl7_18),
% 2.11/0.68    inference(avatar_component_clause,[],[f401])).
% 2.11/0.68  fof(f299,plain,(
% 2.11/0.68    spl7_10),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f298])).
% 2.11/0.68  fof(f298,plain,(
% 2.11/0.68    $false | spl7_10),
% 2.11/0.68    inference(subsumption_resolution,[],[f297,f69])).
% 2.11/0.68  fof(f297,plain,(
% 2.11/0.68    ~l3_lattices(sK0) | spl7_10),
% 2.11/0.68    inference(subsumption_resolution,[],[f296,f66])).
% 2.11/0.68  fof(f296,plain,(
% 2.11/0.68    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_10),
% 2.11/0.68    inference(subsumption_resolution,[],[f295,f67])).
% 2.11/0.68  fof(f295,plain,(
% 2.11/0.68    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_10),
% 2.11/0.68    inference(resolution,[],[f192,f82])).
% 2.11/0.68  fof(f192,plain,(
% 2.11/0.68    ~v9_lattices(sK0) | spl7_10),
% 2.11/0.68    inference(avatar_component_clause,[],[f191])).
% 2.11/0.68  fof(f281,plain,(
% 2.11/0.68    spl7_11),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f280])).
% 2.11/0.68  fof(f280,plain,(
% 2.11/0.68    $false | spl7_11),
% 2.11/0.68    inference(subsumption_resolution,[],[f279,f69])).
% 2.11/0.68  fof(f279,plain,(
% 2.11/0.68    ~l3_lattices(sK0) | spl7_11),
% 2.11/0.68    inference(subsumption_resolution,[],[f278,f66])).
% 2.11/0.68  fof(f278,plain,(
% 2.11/0.68    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_11),
% 2.11/0.68    inference(subsumption_resolution,[],[f277,f67])).
% 2.11/0.68  fof(f277,plain,(
% 2.11/0.68    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_11),
% 2.11/0.68    inference(resolution,[],[f272,f79])).
% 2.11/0.68  fof(f272,plain,(
% 2.11/0.68    ~v6_lattices(sK0) | spl7_11),
% 2.11/0.68    inference(avatar_component_clause,[],[f270])).
% 2.11/0.68  fof(f162,plain,(
% 2.11/0.68    spl7_6),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f161])).
% 2.11/0.68  fof(f161,plain,(
% 2.11/0.68    $false | spl7_6),
% 2.11/0.68    inference(subsumption_resolution,[],[f160,f69])).
% 2.11/0.68  fof(f160,plain,(
% 2.11/0.68    ~l3_lattices(sK0) | spl7_6),
% 2.11/0.68    inference(resolution,[],[f155,f74])).
% 2.11/0.68  fof(f74,plain,(
% 2.11/0.68    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f20])).
% 2.11/0.68  fof(f155,plain,(
% 2.11/0.68    ~l1_lattices(sK0) | spl7_6),
% 2.11/0.68    inference(avatar_component_clause,[],[f153])).
% 2.11/0.68  fof(f159,plain,(
% 2.11/0.68    ~spl7_6 | spl7_7 | ~spl7_5),
% 2.11/0.68    inference(avatar_split_clause,[],[f151,f139,f157,f153])).
% 2.11/0.68  fof(f139,plain,(
% 2.11/0.68    spl7_5 <=> ! [X1,X0] : (r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.11/0.68  fof(f151,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0)) ) | ~spl7_5),
% 2.11/0.68    inference(subsumption_resolution,[],[f150,f66])).
% 2.11/0.68  fof(f150,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_5),
% 2.11/0.68    inference(duplicate_literal_removal,[],[f149])).
% 2.11/0.68  fof(f149,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_5),
% 2.11/0.68    inference(resolution,[],[f140,f100])).
% 2.11/0.68  fof(f140,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_5),
% 2.11/0.68    inference(avatar_component_clause,[],[f139])).
% 2.11/0.68  fof(f144,plain,(
% 2.11/0.68    spl7_4),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f143])).
% 2.11/0.68  fof(f143,plain,(
% 2.11/0.68    $false | spl7_4),
% 2.11/0.68    inference(subsumption_resolution,[],[f142,f69])).
% 2.11/0.68  fof(f142,plain,(
% 2.11/0.68    ~l3_lattices(sK0) | spl7_4),
% 2.11/0.68    inference(resolution,[],[f137,f75])).
% 2.11/0.68  fof(f137,plain,(
% 2.11/0.68    ~l2_lattices(sK0) | spl7_4),
% 2.11/0.68    inference(avatar_component_clause,[],[f135])).
% 2.11/0.68  fof(f141,plain,(
% 2.11/0.68    ~spl7_4 | spl7_5),
% 2.11/0.68    inference(avatar_split_clause,[],[f133,f139,f135])).
% 2.11/0.68  fof(f133,plain,(
% 2.11/0.68    ( ! [X0,X1] : (r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f116,f66])).
% 2.11/0.68  fof(f116,plain,(
% 2.11/0.68    ( ! [X0,X1] : (r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(trivial_inequality_removal,[],[f115])).
% 2.11/0.68  fof(f115,plain,(
% 2.11/0.68    ( ! [X0,X1] : (X1 != X1 | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(duplicate_literal_removal,[],[f114])).
% 2.11/0.68  fof(f114,plain,(
% 2.11/0.68    ( ! [X0,X1] : (X1 != X1 | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(superposition,[],[f87,f112])).
% 2.11/0.68  fof(f112,plain,(
% 2.11/0.68    ( ! [X0,X1] : (k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f111,f66])).
% 2.11/0.68  fof(f111,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1 | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(subsumption_resolution,[],[f110,f69])).
% 2.11/0.68  fof(f110,plain,(
% 2.11/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1 | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 2.11/0.68    inference(resolution,[],[f107,f67])).
% 2.11/0.68  fof(f107,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 | ~l3_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 2.11/0.68    inference(duplicate_literal_removal,[],[f106])).
% 2.11/0.68  fof(f106,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 | ~l3_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 2.11/0.68    inference(resolution,[],[f90,f81])).
% 2.11/0.68  fof(f90,plain,(
% 2.11/0.68    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f59])).
% 2.11/0.68  fof(f59,plain,(
% 2.11/0.68    ! [X0] : (((v8_lattices(X0) | ((sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f56,f58,f57])).
% 2.11/0.68  fof(f57,plain,(
% 2.11/0.68    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 2.11/0.68    introduced(choice_axiom,[])).
% 2.11/0.68  fof(f58,plain,(
% 2.11/0.68    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 2.11/0.68    introduced(choice_axiom,[])).
% 2.11/0.68  fof(f56,plain,(
% 2.11/0.68    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(rectify,[],[f55])).
% 2.11/0.68  fof(f55,plain,(
% 2.11/0.68    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(nnf_transformation,[],[f34])).
% 2.11/0.68  fof(f34,plain,(
% 2.11/0.68    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.11/0.68    inference(flattening,[],[f33])).
% 2.11/0.68  fof(f33,plain,(
% 2.11/0.68    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.11/0.68    inference(ennf_transformation,[],[f3])).
% 2.11/0.68  fof(f3,axiom,(
% 2.11/0.68    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 2.11/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
% 2.11/0.68  % SZS output end Proof for theBenchmark
% 2.11/0.68  % (30110)------------------------------
% 2.11/0.68  % (30110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.68  % (30110)Termination reason: Refutation
% 2.11/0.68  
% 2.11/0.68  % (30110)Memory used [KB]: 11641
% 2.11/0.68  % (30110)Time elapsed: 0.250 s
% 2.11/0.68  % (30110)------------------------------
% 2.11/0.68  % (30110)------------------------------
% 2.11/0.69  % (30106)Success in time 0.322 s
%------------------------------------------------------------------------------
