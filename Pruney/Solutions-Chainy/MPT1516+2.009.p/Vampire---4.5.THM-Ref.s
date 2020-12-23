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
% DateTime   : Thu Dec  3 13:15:49 EST 2020

% Result     : Theorem 29.63s
% Output     : Refutation 29.63s
% Verified   : 
% Statistics : Number of formulae       :  263 (2408 expanded)
%              Number of leaves         :   32 ( 579 expanded)
%              Depth                    :   30
%              Number of atoms          : 1506 (19170 expanded)
%              Number of equality atoms :  198 (2154 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91271,plain,(
    $false ),
    inference(subsumption_resolution,[],[f91270,f89124])).

fof(f89124,plain,(
    v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f89090,f821])).

fof(f821,plain,(
    ! [X15] :
      ( m1_subset_1(sK2(sK0,k16_lattice3(sK0,X15)),u1_struct_0(sK0))
      | v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f820,f108])).

fof(f108,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
          | ~ l3_lattices(X0)
          | ~ v13_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
        | ~ l3_lattices(sK0)
        | ~ v13_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(f820,plain,(
    ! [X15] :
      ( v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,k16_lattice3(sK0,X15)),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f757,f395])).

fof(f395,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f111,f114])).

fof(f114,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f111,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f757,plain,(
    ! [X15] :
      ( v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,k16_lattice3(sK0,X15)),u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f488,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
                  & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f74,f76,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
              & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k2_lattices(X0,X4,X3) = X3
                    & k2_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(f488,plain,(
    ! [X35] : m1_subset_1(k16_lattice3(sK0,X35),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f418,f108])).

fof(f418,plain,(
    ! [X35] :
      ( m1_subset_1(k16_lattice3(sK0,X35),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f111,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f89090,plain,
    ( ~ m1_subset_1(sK2(sK0,k16_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))),u1_struct_0(sK0))
    | v13_lattices(sK0) ),
    inference(resolution,[],[f88976,f24439])).

fof(f24439,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK2(sK0,k16_lattice3(sK0,X5)),a_2_6_lattice3(sK0,X5))
      | v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f24427,f488])).

fof(f24427,plain,(
    ! [X5] :
      ( ~ m1_subset_1(k16_lattice3(sK0,X5),u1_struct_0(sK0))
      | v13_lattices(sK0)
      | ~ r2_hidden(sK2(sK0,k16_lattice3(sK0,X5)),a_2_6_lattice3(sK0,X5)) ) ),
    inference(resolution,[],[f7712,f7104])).

fof(f7104,plain,(
    ! [X2,X3] :
      ( r1_lattices(sK0,k16_lattice3(sK0,X2),X3)
      | ~ r2_hidden(X3,a_2_6_lattice3(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f7076,f1644])).

fof(f1644,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1643,f108])).

fof(f1643,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1642,f109])).

fof(f109,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f1642,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1641,f110])).

fof(f110,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f1641,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1640,f111])).

fof(f1640,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1637])).

fof(f1637,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,a_2_6_lattice3(sK0,X1)) ) ),
    inference(superposition,[],[f165,f504])).

fof(f504,plain,(
    ! [X45,X46] :
      ( sK11(X45,sK0,X46) = X45
      | ~ r2_hidden(X45,a_2_6_lattice3(sK0,X46)) ) ),
    inference(subsumption_resolution,[],[f503,f108])).

fof(f503,plain,(
    ! [X45,X46] :
      ( sK11(X45,sK0,X46) = X45
      | ~ r2_hidden(X45,a_2_6_lattice3(sK0,X46))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f502,f109])).

fof(f502,plain,(
    ! [X45,X46] :
      ( sK11(X45,sK0,X46) = X45
      | ~ r2_hidden(X45,a_2_6_lattice3(sK0,X46))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f424,f110])).

fof(f424,plain,(
    ! [X45,X46] :
      ( sK11(X45,sK0,X46) = X45
      | ~ r2_hidden(X45,a_2_6_lattice3(sK0,X46))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f111,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( sK11(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK12(X0,X1,X2),X2)
            & r3_lattices(X1,sK12(X0,X1,X2),sK11(X0,X1,X2))
            & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))
            & sK11(X0,X1,X2) = X0
            & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f104,f106,f105])).

fof(f105,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r3_lattices(X1,X6,X5)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r3_lattices(X1,X6,sK11(X0,X1,X2))
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK11(X0,X1,X2) = X0
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f106,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,X6,sK11(X0,X1,X2))
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK12(X0,X1,X2),X2)
        & r3_lattices(X1,sK12(X0,X1,X2),sK11(X0,X1,X2))
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r3_lattices(X1,X6,X5)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X1,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_6_lattice3)).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f7076,plain,(
    ! [X2,X3] :
      ( r1_lattices(sK0,k16_lattice3(sK0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_6_lattice3(sK0,X2)) ) ),
    inference(superposition,[],[f3420,f453])).

fof(f453,plain,(
    ! [X6] : k16_lattice3(sK0,X6) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X6)) ),
    inference(subsumption_resolution,[],[f452,f108])).

fof(f452,plain,(
    ! [X6] :
      ( k16_lattice3(sK0,X6) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X6))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f451,f109])).

fof(f451,plain,(
    ! [X6] :
      ( k16_lattice3(sK0,X6) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X6))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f403,f110])).

fof(f403,plain,(
    ! [X6] :
      ( k16_lattice3(sK0,X6) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X6))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f111,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

fof(f3420,plain,(
    ! [X10,X9] :
      ( r1_lattices(sK0,k16_lattice3(sK0,X10),X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ r2_hidden(X9,X10) ) ),
    inference(subsumption_resolution,[],[f3419,f108])).

fof(f3419,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r1_lattices(sK0,k16_lattice3(sK0,X10),X9)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3418,f109])).

fof(f3418,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r1_lattices(sK0,k16_lattice3(sK0,X10),X9)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3417,f110])).

fof(f3417,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r1_lattices(sK0,k16_lattice3(sK0,X10),X9)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3416,f111])).

fof(f3416,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r1_lattices(sK0,k16_lattice3(sK0,X10),X9)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f3408,f488])).

fof(f3408,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r1_lattices(sK0,k16_lattice3(sK0,X10),X9)
      | ~ m1_subset_1(k16_lattice3(sK0,X10),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3401])).

fof(f3401,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | r1_lattices(sK0,k16_lattice3(sK0,X10),X9)
      | ~ m1_subset_1(k16_lattice3(sK0,X10),u1_struct_0(sK0))
      | ~ m1_subset_1(k16_lattice3(sK0,X10),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f484,f174])).

fof(f174,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK6(X0,X1,X2),X2)
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f85,f86])).

fof(f86,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
        & r3_lattice3(X0,sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f484,plain,(
    ! [X28,X26,X27] :
      ( ~ r3_lattice3(sK0,X26,X28)
      | ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X27,u1_struct_0(sK0))
      | r1_lattices(sK0,X26,X27)
      | ~ m1_subset_1(X26,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f414,f108])).

fof(f414,plain,(
    ! [X28,X26,X27] :
      ( r1_lattices(sK0,X26,X27)
      | ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X27,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X26,X28)
      | ~ m1_subset_1(X26,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f111,f155])).

fof(f155,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK9(X0,X1,X2))
                  & r2_hidden(sK9(X0,X1,X2),X2)
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f96,f97])).

fof(f97,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(f7712,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK0,X0,sK2(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f7711,f2491])).

fof(f2491,plain,(
    ! [X8] :
      ( m1_subset_1(sK2(sK0,X8),u1_struct_0(sK0))
      | v13_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f195,f395])).

fof(f195,plain,(
    ! [X8] :
      ( v13_lattices(sK0)
      | m1_subset_1(sK2(sK0,X8),u1_struct_0(sK0))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ l1_lattices(sK0) ) ),
    inference(resolution,[],[f108,f129])).

fof(f7711,plain,(
    ! [X0] :
      ( v13_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X0,sK2(sK0,X0))
      | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) ) ),
    inference(trivial_inequality_removal,[],[f7710])).

fof(f7710,plain,(
    ! [X0] :
      ( X0 != X0
      | v13_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X0,sK2(sK0,X0))
      | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f7701])).

fof(f7701,plain,(
    ! [X0] :
      ( X0 != X0
      | v13_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X0,sK2(sK0,X0))
      | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f4031,f4210])).

fof(f4210,plain,(
    ! [X0,X1] :
      ( k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f4209,f440])).

fof(f440,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f439,f108])).

fof(f439,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f397,f109])).

fof(f397,plain,
    ( v8_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f111,f117])).

fof(f117,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f4209,plain,(
    ! [X0,X1] :
      ( k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f443,f442])).

fof(f442,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f441,f108])).

fof(f441,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f398,f109])).

fof(f398,plain,
    ( v9_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f111,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f443,plain,(
    ! [X0,X1] :
      ( k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f399,f108])).

fof(f399,plain,(
    ! [X0,X1] :
      ( k2_lattices(sK0,X0,X1) = X0
      | ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f111,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f4031,plain,(
    ! [X16] :
      ( k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | v13_lattices(sK0)
      | ~ m1_subset_1(X16,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f4030,f2491])).

fof(f4030,plain,(
    ! [X16] :
      ( k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | v13_lattices(sK0)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f4029,f108])).

fof(f4029,plain,(
    ! [X16] :
      ( k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | v13_lattices(sK0)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3987,f395])).

fof(f3987,plain,(
    ! [X16] :
      ( k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | v13_lattices(sK0)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f3960])).

fof(f3960,plain,(
    ! [X16] :
      ( k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | v13_lattices(sK0)
      | k2_lattices(sK0,X16,sK2(sK0,X16)) != X16
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0))
      | ~ m1_subset_1(X16,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f130,f3928])).

fof(f3928,plain,(
    ! [X10,X11] :
      ( k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3927,f395])).

fof(f3927,plain,(
    ! [X10,X11] :
      ( k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ l1_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f197,f438])).

fof(f438,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f437,f108])).

fof(f437,plain,
    ( v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f396,f109])).

fof(f396,plain,
    ( v6_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f111,f116])).

fof(f116,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f197,plain,(
    ! [X10,X11] :
      ( k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0) ) ),
    inference(resolution,[],[f108,f131])).

fof(f131,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f79,f81,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(f130,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f88976,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f9600,f1250])).

fof(f1250,plain,(
    ! [X0] : r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0)) ),
    inference(subsumption_resolution,[],[f1249,f108])).

fof(f1249,plain,(
    ! [X0] :
      ( r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1248,f109])).

fof(f1248,plain,(
    ! [X0] :
      ( r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1247,f110])).

fof(f1247,plain,(
    ! [X0] :
      ( r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1246,f111])).

fof(f1246,plain,(
    ! [X0] :
      ( r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1235,f489])).

fof(f489,plain,(
    ! [X36] : m1_subset_1(k15_lattice3(sK0,X36),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f419,f108])).

fof(f419,plain,(
    ! [X36] :
      ( m1_subset_1(k15_lattice3(sK0,X36),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f111,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f1235,plain,(
    ! [X0] :
      ( r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f946,f177])).

fof(f177,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f164])).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK10(X0,X1,X2),X2)
            & sK10(X0,X1,X2) = X0
            & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f100,f101])).

fof(f101,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK10(X0,X1,X2),X2)
        & sK10(X0,X1,X2) = X0
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r4_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r4_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f946,plain,(
    ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) ),
    inference(subsumption_resolution,[],[f945,f108])).

fof(f945,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f944,f109])).

fof(f944,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f943,f110])).

fof(f943,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f903,f111])).

fof(f903,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f489,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK8(X0,X1,X2))
                & r4_lattice3(X0,sK8(X0,X1,X2),X1)
                & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f92,f93])).

fof(f93,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK8(X0,X1,X2))
        & r4_lattice3(X0,sK8(X0,X1,X2),X1)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(f9600,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1)
      | r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f9599,f108])).

fof(f9599,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f9598,f109])).

fof(f9598,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f9597,f110])).

fof(f9597,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f9596,f111])).

fof(f9596,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f9595,f489])).

fof(f9595,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1)
      | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f9591])).

fof(f9591,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_6_lattice3(sK0,X1))
      | ~ r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1)
      | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f9589,f178])).

fof(f178,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X3,a_2_6_lattice3(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r3_lattices(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f170])).

fof(f170,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r3_lattices(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f9589,plain,(
    ! [X0] :
      ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1541,f113])).

fof(f113,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1541,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,k6_domain_1(u1_struct_0(sK0),X4))
      | r3_lattices(sK0,k15_lattice3(sK0,X5),X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1540,f108])).

fof(f1540,plain,(
    ! [X4,X5] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X5),X4)
      | ~ r1_tarski(X5,k6_domain_1(u1_struct_0(sK0),X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1539,f109])).

fof(f1539,plain,(
    ! [X4,X5] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X5),X4)
      | ~ r1_tarski(X5,k6_domain_1(u1_struct_0(sK0),X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1538,f110])).

fof(f1538,plain,(
    ! [X4,X5] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X5),X4)
      | ~ r1_tarski(X5,k6_domain_1(u1_struct_0(sK0),X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1504,f111])).

fof(f1504,plain,(
    ! [X4,X5] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X5),X4)
      | ~ r1_tarski(X5,k6_domain_1(u1_struct_0(sK0),X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f471,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).

fof(f471,plain,(
    ! [X15,X16] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X15),k15_lattice3(sK0,X16))
      | ~ r1_tarski(X15,X16) ) ),
    inference(subsumption_resolution,[],[f470,f108])).

fof(f470,plain,(
    ! [X15,X16] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X15),k15_lattice3(sK0,X16))
      | ~ r1_tarski(X15,X16)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f469,f109])).

fof(f469,plain,(
    ! [X15,X16] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X15),k15_lattice3(sK0,X16))
      | ~ r1_tarski(X15,X16)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f409,f110])).

fof(f409,plain,(
    ! [X15,X16] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X15),k15_lattice3(sK0,X16))
      | ~ r1_tarski(X15,X16)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f111,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

fof(f91270,plain,(
    ~ v13_lattices(sK0) ),
    inference(trivial_inequality_removal,[],[f90952])).

fof(f90952,plain,
    ( k5_lattices(sK0) != k5_lattices(sK0)
    | ~ v13_lattices(sK0) ),
    inference(backward_demodulation,[],[f543,f90821])).

fof(f90821,plain,(
    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f90820,f89124])).

fof(f90820,plain,
    ( ~ v13_lattices(sK0)
    | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f90772,f558])).

fof(f558,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f544,f108])).

fof(f544,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f395,f121])).

fof(f121,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f90772,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    inference(resolution,[],[f89066,f6089])).

fof(f6089,plain,(
    ! [X2] :
      ( ~ r1_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
      | ~ v13_lattices(sK0)
      | k5_lattices(sK0) = k15_lattice3(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f6088,f489])).

fof(f6088,plain,(
    ! [X2] :
      ( k5_lattices(sK0) = k15_lattice3(sK0,X2)
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f6068,f558])).

fof(f6068,plain,(
    ! [X2] :
      ( k5_lattices(sK0) = k15_lattice3(sK0,X2)
      | ~ v13_lattices(sK0)
      | ~ r1_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f1021,f4210])).

fof(f1021,plain,(
    ! [X44] :
      ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X44),k5_lattices(sK0))
      | ~ v13_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f1020,f108])).

fof(f1020,plain,(
    ! [X44] :
      ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X44),k5_lattices(sK0))
      | ~ v13_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1019,f395])).

fof(f1019,plain,(
    ! [X44] :
      ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X44),k5_lattices(sK0))
      | ~ v13_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f928,f558])).

fof(f928,plain,(
    ! [X44] :
      ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X44),k5_lattices(sK0))
      | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
      | ~ v13_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f489,f171])).

fof(f171,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f70,f71])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f89066,plain,(
    ! [X0] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f88976,f8701])).

fof(f8701,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X1)))
      | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) ) ),
    inference(subsumption_resolution,[],[f8700,f1644])).

fof(f8700,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) ) ),
    inference(subsumption_resolution,[],[f8683,f489])).

fof(f8683,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f2430,f484])).

fof(f2430,plain,(
    ! [X0] : r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X0))) ),
    inference(superposition,[],[f1489,f447])).

fof(f447,plain,(
    ! [X4] : k15_lattice3(sK0,X4) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X4)) ),
    inference(subsumption_resolution,[],[f446,f108])).

fof(f446,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X4))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f445,f109])).

fof(f445,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X4))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f401,f110])).

fof(f401,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X4))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f111,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(f1489,plain,(
    ! [X18] : r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18)) ),
    inference(subsumption_resolution,[],[f1488,f108])).

fof(f1488,plain,(
    ! [X18] :
      ( r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1487,f109])).

fof(f1487,plain,(
    ! [X18] :
      ( r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1486,f110])).

fof(f1486,plain,(
    ! [X18] :
      ( r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1485,f111])).

fof(f1485,plain,(
    ! [X18] :
      ( r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1441,f488])).

fof(f1441,plain,(
    ! [X18] :
      ( ~ m1_subset_1(k16_lattice3(sK0,X18),u1_struct_0(sK0))
      | r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f174,f453])).

fof(f543,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0) ),
    inference(subsumption_resolution,[],[f542,f108])).

fof(f542,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f541,f109])).

fof(f541,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f111])).

fof(f112,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:11 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.47  % (4440)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.47  % (4440)Refutation not found, incomplete strategy% (4440)------------------------------
% 0.21/0.47  % (4440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (4440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (4440)Memory used [KB]: 10618
% 0.21/0.47  % (4440)Time elapsed: 0.056 s
% 0.21/0.47  % (4440)------------------------------
% 0.21/0.47  % (4440)------------------------------
% 0.21/0.47  % (4450)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.48  % (4448)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.48  % (4442)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (4442)Refutation not found, incomplete strategy% (4442)------------------------------
% 0.21/0.48  % (4442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4442)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4442)Memory used [KB]: 6140
% 0.21/0.48  % (4442)Time elapsed: 0.002 s
% 0.21/0.48  % (4442)------------------------------
% 0.21/0.48  % (4442)------------------------------
% 0.21/0.49  % (4432)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (4430)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (4449)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (4431)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (4439)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (4452)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (4434)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (4433)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (4453)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (4436)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (4441)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (4438)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (4451)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (4437)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (4429)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (4429)Refutation not found, incomplete strategy% (4429)------------------------------
% 0.21/0.54  % (4429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4429)Memory used [KB]: 10618
% 0.21/0.54  % (4429)Time elapsed: 0.118 s
% 0.21/0.54  % (4429)------------------------------
% 0.21/0.54  % (4429)------------------------------
% 0.21/0.54  % (4454)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (4446)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (4435)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (4435)Refutation not found, incomplete strategy% (4435)------------------------------
% 0.21/0.54  % (4435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4435)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4435)Memory used [KB]: 10490
% 0.21/0.54  % (4435)Time elapsed: 0.001 s
% 0.21/0.54  % (4435)------------------------------
% 0.21/0.54  % (4435)------------------------------
% 0.21/0.55  % (4443)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (4445)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.56  % (4444)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.56  % (4447)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 2.28/0.67  % (4438)Refutation not found, incomplete strategy% (4438)------------------------------
% 2.28/0.67  % (4438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.67  % (4438)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.67  
% 2.28/0.67  % (4438)Memory used [KB]: 6140
% 2.28/0.67  % (4438)Time elapsed: 0.264 s
% 2.28/0.67  % (4438)------------------------------
% 2.28/0.67  % (4438)------------------------------
% 2.28/0.69  % (4446)Refutation not found, incomplete strategy% (4446)------------------------------
% 2.28/0.69  % (4446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.69  % (4446)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.69  
% 2.28/0.69  % (4446)Memory used [KB]: 6268
% 2.28/0.69  % (4446)Time elapsed: 0.280 s
% 2.28/0.69  % (4446)------------------------------
% 2.28/0.69  % (4446)------------------------------
% 4.54/0.93  % (4443)Time limit reached!
% 4.54/0.93  % (4443)------------------------------
% 4.54/0.93  % (4443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.93  % (4443)Termination reason: Time limit
% 4.54/0.93  % (4443)Termination phase: Saturation
% 4.54/0.93  
% 4.54/0.93  % (4443)Memory used [KB]: 9210
% 4.54/0.93  % (4443)Time elapsed: 0.500 s
% 4.54/0.93  % (4443)------------------------------
% 4.54/0.93  % (4443)------------------------------
% 7.58/1.32  % (4437)Time limit reached!
% 7.58/1.32  % (4437)------------------------------
% 7.58/1.32  % (4437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.58/1.32  % (4437)Termination reason: Time limit
% 7.58/1.32  
% 7.58/1.32  % (4437)Memory used [KB]: 7036
% 7.58/1.32  % (4437)Time elapsed: 0.916 s
% 7.58/1.32  % (4437)------------------------------
% 7.58/1.32  % (4437)------------------------------
% 8.10/1.42  % (4430)Time limit reached!
% 8.10/1.42  % (4430)------------------------------
% 8.10/1.42  % (4430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.10/1.43  % (4430)Termination reason: Time limit
% 8.10/1.43  
% 8.10/1.43  % (4430)Memory used [KB]: 19701
% 8.10/1.43  % (4430)Time elapsed: 1.011 s
% 8.10/1.43  % (4430)------------------------------
% 8.10/1.43  % (4430)------------------------------
% 9.41/1.55  % (4433)Time limit reached!
% 9.41/1.55  % (4433)------------------------------
% 9.41/1.55  % (4433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.41/1.55  % (4433)Termination reason: Time limit
% 9.41/1.55  
% 9.41/1.55  % (4433)Memory used [KB]: 11513
% 9.41/1.55  % (4433)Time elapsed: 1.134 s
% 9.41/1.55  % (4433)------------------------------
% 9.41/1.55  % (4433)------------------------------
% 29.63/4.10  % (4447)Refutation found. Thanks to Tanya!
% 29.63/4.10  % SZS status Theorem for theBenchmark
% 29.63/4.11  % (4434)Time limit reached!
% 29.63/4.11  % (4434)------------------------------
% 29.63/4.11  % (4434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.63/4.11  % (4434)Termination reason: Time limit
% 29.63/4.11  % (4434)Termination phase: Saturation
% 29.63/4.11  
% 29.63/4.11  % (4434)Memory used [KB]: 25841
% 29.63/4.11  % (4434)Time elapsed: 3.700 s
% 29.63/4.11  % (4434)------------------------------
% 29.63/4.11  % (4434)------------------------------
% 29.63/4.11  % SZS output start Proof for theBenchmark
% 29.63/4.11  fof(f91271,plain,(
% 29.63/4.11    $false),
% 29.63/4.11    inference(subsumption_resolution,[],[f91270,f89124])).
% 29.63/4.11  fof(f89124,plain,(
% 29.63/4.11    v13_lattices(sK0)),
% 29.63/4.11    inference(subsumption_resolution,[],[f89090,f821])).
% 29.63/4.11  fof(f821,plain,(
% 29.63/4.11    ( ! [X15] : (m1_subset_1(sK2(sK0,k16_lattice3(sK0,X15)),u1_struct_0(sK0)) | v13_lattices(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f820,f108])).
% 29.63/4.11  fof(f108,plain,(
% 29.63/4.11    ~v2_struct_0(sK0)),
% 29.63/4.11    inference(cnf_transformation,[],[f67])).
% 29.63/4.11  fof(f67,plain,(
% 29.63/4.11    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 29.63/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f66])).
% 29.63/4.11  fof(f66,plain,(
% 29.63/4.11    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 29.63/4.11    introduced(choice_axiom,[])).
% 29.63/4.11  fof(f28,plain,(
% 29.63/4.11    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 29.63/4.11    inference(flattening,[],[f27])).
% 29.63/4.11  fof(f27,plain,(
% 29.63/4.11    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 29.63/4.11    inference(ennf_transformation,[],[f22])).
% 29.63/4.11  fof(f22,negated_conjecture,(
% 29.63/4.11    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 29.63/4.11    inference(negated_conjecture,[],[f21])).
% 29.63/4.11  fof(f21,conjecture,(
% 29.63/4.11    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 29.63/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 29.63/4.11  fof(f820,plain,(
% 29.63/4.11    ( ! [X15] : (v13_lattices(sK0) | m1_subset_1(sK2(sK0,k16_lattice3(sK0,X15)),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f757,f395])).
% 29.63/4.11  fof(f395,plain,(
% 29.63/4.11    l1_lattices(sK0)),
% 29.63/4.11    inference(resolution,[],[f111,f114])).
% 29.63/4.11  fof(f114,plain,(
% 29.63/4.11    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f29])).
% 29.63/4.11  fof(f29,plain,(
% 29.63/4.11    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 29.63/4.11    inference(ennf_transformation,[],[f23])).
% 29.63/4.11  fof(f23,plain,(
% 29.63/4.11    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 29.63/4.11    inference(pure_predicate_removal,[],[f5])).
% 29.63/4.11  fof(f5,axiom,(
% 29.63/4.11    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 29.63/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 29.63/4.11  fof(f111,plain,(
% 29.63/4.11    l3_lattices(sK0)),
% 29.63/4.11    inference(cnf_transformation,[],[f67])).
% 29.63/4.11  fof(f757,plain,(
% 29.63/4.11    ( ! [X15] : (v13_lattices(sK0) | m1_subset_1(sK2(sK0,k16_lattice3(sK0,X15)),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(resolution,[],[f488,f129])).
% 29.63/4.11  fof(f129,plain,(
% 29.63/4.11    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f77])).
% 29.63/4.11  fof(f77,plain,(
% 29.63/4.11    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f74,f76,f75])).
% 29.63/4.11  fof(f75,plain,(
% 29.63/4.11    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 29.63/4.11    introduced(choice_axiom,[])).
% 29.63/4.11  fof(f76,plain,(
% 29.63/4.11    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 29.63/4.11    introduced(choice_axiom,[])).
% 29.63/4.11  fof(f74,plain,(
% 29.63/4.11    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(rectify,[],[f73])).
% 29.63/4.11  fof(f73,plain,(
% 29.63/4.11    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(nnf_transformation,[],[f39])).
% 29.63/4.11  fof(f39,plain,(
% 29.63/4.11    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(flattening,[],[f38])).
% 29.63/4.11  fof(f38,plain,(
% 29.63/4.11    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.11    inference(ennf_transformation,[],[f7])).
% 29.63/4.11  fof(f7,axiom,(
% 29.63/4.11    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 29.63/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 29.63/4.11  fof(f488,plain,(
% 29.63/4.11    ( ! [X35] : (m1_subset_1(k16_lattice3(sK0,X35),u1_struct_0(sK0))) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f418,f108])).
% 29.63/4.11  fof(f418,plain,(
% 29.63/4.11    ( ! [X35] : (m1_subset_1(k16_lattice3(sK0,X35),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(resolution,[],[f111,f159])).
% 29.63/4.11  fof(f159,plain,(
% 29.63/4.11    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f59])).
% 29.63/4.11  fof(f59,plain,(
% 29.63/4.11    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(flattening,[],[f58])).
% 29.63/4.11  fof(f58,plain,(
% 29.63/4.11    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.11    inference(ennf_transformation,[],[f12])).
% 29.63/4.11  fof(f12,axiom,(
% 29.63/4.11    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 29.63/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 29.63/4.11  fof(f89090,plain,(
% 29.63/4.11    ~m1_subset_1(sK2(sK0,k16_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))),u1_struct_0(sK0)) | v13_lattices(sK0)),
% 29.63/4.11    inference(resolution,[],[f88976,f24439])).
% 29.63/4.11  fof(f24439,plain,(
% 29.63/4.11    ( ! [X5] : (~r2_hidden(sK2(sK0,k16_lattice3(sK0,X5)),a_2_6_lattice3(sK0,X5)) | v13_lattices(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f24427,f488])).
% 29.63/4.11  fof(f24427,plain,(
% 29.63/4.11    ( ! [X5] : (~m1_subset_1(k16_lattice3(sK0,X5),u1_struct_0(sK0)) | v13_lattices(sK0) | ~r2_hidden(sK2(sK0,k16_lattice3(sK0,X5)),a_2_6_lattice3(sK0,X5))) )),
% 29.63/4.11    inference(resolution,[],[f7712,f7104])).
% 29.63/4.11  fof(f7104,plain,(
% 29.63/4.11    ( ! [X2,X3] : (r1_lattices(sK0,k16_lattice3(sK0,X2),X3) | ~r2_hidden(X3,a_2_6_lattice3(sK0,X2))) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f7076,f1644])).
% 29.63/4.11  fof(f1644,plain,(
% 29.63/4.11    ( ! [X0,X1] : (~r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f1643,f108])).
% 29.63/4.11  fof(f1643,plain,(
% 29.63/4.11    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f1642,f109])).
% 29.63/4.11  fof(f109,plain,(
% 29.63/4.11    v10_lattices(sK0)),
% 29.63/4.11    inference(cnf_transformation,[],[f67])).
% 29.63/4.11  fof(f1642,plain,(
% 29.63/4.11    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f1641,f110])).
% 29.63/4.11  fof(f110,plain,(
% 29.63/4.11    v4_lattice3(sK0)),
% 29.63/4.11    inference(cnf_transformation,[],[f67])).
% 29.63/4.11  fof(f1641,plain,(
% 29.63/4.11    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f1640,f111])).
% 29.63/4.11  fof(f1640,plain,(
% 29.63/4.11    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(duplicate_literal_removal,[],[f1637])).
% 29.63/4.11  fof(f1637,plain,(
% 29.63/4.11    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~r2_hidden(X0,a_2_6_lattice3(sK0,X1))) )),
% 29.63/4.11    inference(superposition,[],[f165,f504])).
% 29.63/4.11  fof(f504,plain,(
% 29.63/4.11    ( ! [X45,X46] : (sK11(X45,sK0,X46) = X45 | ~r2_hidden(X45,a_2_6_lattice3(sK0,X46))) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f503,f108])).
% 29.63/4.11  fof(f503,plain,(
% 29.63/4.11    ( ! [X45,X46] : (sK11(X45,sK0,X46) = X45 | ~r2_hidden(X45,a_2_6_lattice3(sK0,X46)) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f502,f109])).
% 29.63/4.11  fof(f502,plain,(
% 29.63/4.11    ( ! [X45,X46] : (sK11(X45,sK0,X46) = X45 | ~r2_hidden(X45,a_2_6_lattice3(sK0,X46)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f424,f110])).
% 29.63/4.11  fof(f424,plain,(
% 29.63/4.11    ( ! [X45,X46] : (sK11(X45,sK0,X46) = X45 | ~r2_hidden(X45,a_2_6_lattice3(sK0,X46)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(resolution,[],[f111,f166])).
% 29.63/4.11  fof(f166,plain,(
% 29.63/4.11    ( ! [X2,X0,X1] : (sK11(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f107])).
% 29.63/4.11  fof(f107,plain,(
% 29.63/4.11    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK12(X0,X1,X2),X2) & r3_lattices(X1,sK12(X0,X1,X2),sK11(X0,X1,X2)) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))) & sK11(X0,X1,X2) = X0 & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 29.63/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f104,f106,f105])).
% 29.63/4.11  fof(f105,plain,(
% 29.63/4.11    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,sK11(X0,X1,X2)) & m1_subset_1(X6,u1_struct_0(X1))) & sK11(X0,X1,X2) = X0 & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))))),
% 29.63/4.11    introduced(choice_axiom,[])).
% 29.63/4.11  fof(f106,plain,(
% 29.63/4.11    ! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,sK11(X0,X1,X2)) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK12(X0,X1,X2),X2) & r3_lattices(X1,sK12(X0,X1,X2),sK11(X0,X1,X2)) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))))),
% 29.63/4.11    introduced(choice_axiom,[])).
% 29.63/4.11  fof(f104,plain,(
% 29.63/4.11    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 29.63/4.11    inference(rectify,[],[f103])).
% 29.63/4.11  fof(f103,plain,(
% 29.63/4.11    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 29.63/4.11    inference(nnf_transformation,[],[f65])).
% 29.63/4.11  fof(f65,plain,(
% 29.63/4.11    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 29.63/4.11    inference(flattening,[],[f64])).
% 29.63/4.11  fof(f64,plain,(
% 29.63/4.11    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 29.63/4.11    inference(ennf_transformation,[],[f14])).
% 29.63/4.11  fof(f14,axiom,(
% 29.63/4.11    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 29.63/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_6_lattice3)).
% 29.63/4.11  fof(f165,plain,(
% 29.63/4.11    ( ! [X2,X0,X1] : (m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f107])).
% 29.63/4.11  fof(f7076,plain,(
% 29.63/4.11    ( ! [X2,X3] : (r1_lattices(sK0,k16_lattice3(sK0,X2),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_6_lattice3(sK0,X2))) )),
% 29.63/4.11    inference(superposition,[],[f3420,f453])).
% 29.63/4.11  fof(f453,plain,(
% 29.63/4.11    ( ! [X6] : (k16_lattice3(sK0,X6) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X6))) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f452,f108])).
% 29.63/4.11  fof(f452,plain,(
% 29.63/4.11    ( ! [X6] : (k16_lattice3(sK0,X6) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X6)) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f451,f109])).
% 29.63/4.11  fof(f451,plain,(
% 29.63/4.11    ( ! [X6] : (k16_lattice3(sK0,X6) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X6)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f403,f110])).
% 29.63/4.11  fof(f403,plain,(
% 29.63/4.11    ( ! [X6] : (k16_lattice3(sK0,X6) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X6)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(resolution,[],[f111,f137])).
% 29.63/4.11  fof(f137,plain,(
% 29.63/4.11    ( ! [X0,X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f45])).
% 29.63/4.11  fof(f45,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(flattening,[],[f44])).
% 29.63/4.11  fof(f44,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.11    inference(ennf_transformation,[],[f19])).
% 29.63/4.11  fof(f19,axiom,(
% 29.63/4.11    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 29.63/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).
% 29.63/4.11  fof(f3420,plain,(
% 29.63/4.11    ( ! [X10,X9] : (r1_lattices(sK0,k16_lattice3(sK0,X10),X9) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~r2_hidden(X9,X10)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f3419,f108])).
% 29.63/4.11  fof(f3419,plain,(
% 29.63/4.11    ( ! [X10,X9] : (~r2_hidden(X9,X10) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,X10),X9) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f3418,f109])).
% 29.63/4.11  fof(f3418,plain,(
% 29.63/4.11    ( ! [X10,X9] : (~r2_hidden(X9,X10) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,X10),X9) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f3417,f110])).
% 29.63/4.11  fof(f3417,plain,(
% 29.63/4.11    ( ! [X10,X9] : (~r2_hidden(X9,X10) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,X10),X9) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f3416,f111])).
% 29.63/4.11  fof(f3416,plain,(
% 29.63/4.11    ( ! [X10,X9] : (~r2_hidden(X9,X10) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,X10),X9) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f3408,f488])).
% 29.63/4.11  fof(f3408,plain,(
% 29.63/4.11    ( ! [X10,X9] : (~r2_hidden(X9,X10) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,X10),X9) | ~m1_subset_1(k16_lattice3(sK0,X10),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(duplicate_literal_removal,[],[f3401])).
% 29.63/4.11  fof(f3401,plain,(
% 29.63/4.11    ( ! [X10,X9] : (~r2_hidden(X9,X10) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,X10),X9) | ~m1_subset_1(k16_lattice3(sK0,X10),u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,X10),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(resolution,[],[f484,f174])).
% 29.63/4.11  fof(f174,plain,(
% 29.63/4.11    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.11    inference(equality_resolution,[],[f140])).
% 29.63/4.11  fof(f140,plain,(
% 29.63/4.11    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f87])).
% 29.63/4.11  fof(f87,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f85,f86])).
% 29.63/4.11  fof(f86,plain,(
% 29.63/4.11    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 29.63/4.11    introduced(choice_axiom,[])).
% 29.63/4.11  fof(f85,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(rectify,[],[f84])).
% 29.63/4.11  fof(f84,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(flattening,[],[f83])).
% 29.63/4.11  fof(f83,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(nnf_transformation,[],[f49])).
% 29.63/4.11  fof(f49,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(flattening,[],[f48])).
% 29.63/4.11  fof(f48,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.11    inference(ennf_transformation,[],[f15])).
% 29.63/4.11  fof(f15,axiom,(
% 29.63/4.11    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 29.63/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 29.63/4.11  fof(f484,plain,(
% 29.63/4.11    ( ! [X28,X26,X27] : (~r3_lattice3(sK0,X26,X28) | ~r2_hidden(X27,X28) | ~m1_subset_1(X27,u1_struct_0(sK0)) | r1_lattices(sK0,X26,X27) | ~m1_subset_1(X26,u1_struct_0(sK0))) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f414,f108])).
% 29.63/4.11  fof(f414,plain,(
% 29.63/4.11    ( ! [X28,X26,X27] : (r1_lattices(sK0,X26,X27) | ~r2_hidden(X27,X28) | ~m1_subset_1(X27,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X26,X28) | ~m1_subset_1(X26,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(resolution,[],[f111,f155])).
% 29.63/4.11  fof(f155,plain,(
% 29.63/4.11    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f98])).
% 29.63/4.11  fof(f98,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f96,f97])).
% 29.63/4.11  fof(f97,plain,(
% 29.63/4.11    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))))),
% 29.63/4.11    introduced(choice_axiom,[])).
% 29.63/4.11  fof(f96,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(rectify,[],[f95])).
% 29.63/4.11  fof(f95,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(nnf_transformation,[],[f57])).
% 29.63/4.11  fof(f57,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(flattening,[],[f56])).
% 29.63/4.11  fof(f56,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.11    inference(ennf_transformation,[],[f8])).
% 29.63/4.11  fof(f8,axiom,(
% 29.63/4.11    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 29.63/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 29.63/4.11  fof(f7712,plain,(
% 29.63/4.11    ( ! [X0] : (~r1_lattices(sK0,X0,sK2(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v13_lattices(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f7711,f2491])).
% 29.63/4.11  fof(f2491,plain,(
% 29.63/4.11    ( ! [X8] : (m1_subset_1(sK2(sK0,X8),u1_struct_0(sK0)) | v13_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0))) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f195,f395])).
% 29.63/4.11  fof(f195,plain,(
% 29.63/4.11    ( ! [X8] : (v13_lattices(sK0) | m1_subset_1(sK2(sK0,X8),u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~l1_lattices(sK0)) )),
% 29.63/4.11    inference(resolution,[],[f108,f129])).
% 29.63/4.11  fof(f7711,plain,(
% 29.63/4.11    ( ! [X0] : (v13_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattices(sK0,X0,sK2(sK0,X0)) | ~m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))) )),
% 29.63/4.11    inference(trivial_inequality_removal,[],[f7710])).
% 29.63/4.11  fof(f7710,plain,(
% 29.63/4.11    ( ! [X0] : (X0 != X0 | v13_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattices(sK0,X0,sK2(sK0,X0)) | ~m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))) )),
% 29.63/4.11    inference(duplicate_literal_removal,[],[f7701])).
% 29.63/4.11  fof(f7701,plain,(
% 29.63/4.11    ( ! [X0] : (X0 != X0 | v13_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattices(sK0,X0,sK2(sK0,X0)) | ~m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 29.63/4.11    inference(superposition,[],[f4031,f4210])).
% 29.63/4.11  fof(f4210,plain,(
% 29.63/4.11    ( ! [X0,X1] : (k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f4209,f440])).
% 29.63/4.11  fof(f440,plain,(
% 29.63/4.11    v8_lattices(sK0)),
% 29.63/4.11    inference(subsumption_resolution,[],[f439,f108])).
% 29.63/4.11  fof(f439,plain,(
% 29.63/4.11    v8_lattices(sK0) | v2_struct_0(sK0)),
% 29.63/4.11    inference(subsumption_resolution,[],[f397,f109])).
% 29.63/4.11  fof(f397,plain,(
% 29.63/4.11    v8_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 29.63/4.11    inference(resolution,[],[f111,f117])).
% 29.63/4.11  fof(f117,plain,(
% 29.63/4.11    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f31])).
% 29.63/4.11  fof(f31,plain,(
% 29.63/4.11    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 29.63/4.11    inference(flattening,[],[f30])).
% 29.63/4.11  fof(f30,plain,(
% 29.63/4.11    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 29.63/4.11    inference(ennf_transformation,[],[f26])).
% 29.63/4.11  fof(f26,plain,(
% 29.63/4.11    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 29.63/4.11    inference(pure_predicate_removal,[],[f25])).
% 29.63/4.11  fof(f25,plain,(
% 29.63/4.11    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 29.63/4.11    inference(pure_predicate_removal,[],[f24])).
% 29.63/4.11  fof(f24,plain,(
% 29.63/4.11    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 29.63/4.11    inference(pure_predicate_removal,[],[f2])).
% 29.63/4.11  fof(f2,axiom,(
% 29.63/4.11    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 29.63/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 29.63/4.11  fof(f4209,plain,(
% 29.63/4.11    ( ! [X0,X1] : (k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v8_lattices(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f443,f442])).
% 29.63/4.11  fof(f442,plain,(
% 29.63/4.11    v9_lattices(sK0)),
% 29.63/4.11    inference(subsumption_resolution,[],[f441,f108])).
% 29.63/4.11  fof(f441,plain,(
% 29.63/4.11    v9_lattices(sK0) | v2_struct_0(sK0)),
% 29.63/4.11    inference(subsumption_resolution,[],[f398,f109])).
% 29.63/4.11  fof(f398,plain,(
% 29.63/4.11    v9_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 29.63/4.11    inference(resolution,[],[f111,f118])).
% 29.63/4.11  fof(f118,plain,(
% 29.63/4.11    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f31])).
% 29.63/4.11  fof(f443,plain,(
% 29.63/4.11    ( ! [X0,X1] : (k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0)) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f399,f108])).
% 29.63/4.11  fof(f399,plain,(
% 29.63/4.11    ( ! [X0,X1] : (k2_lattices(sK0,X0,X1) = X0 | ~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.11    inference(resolution,[],[f111,f119])).
% 29.63/4.11  fof(f119,plain,(
% 29.63/4.11    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.11    inference(cnf_transformation,[],[f68])).
% 29.63/4.11  fof(f68,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(nnf_transformation,[],[f33])).
% 29.63/4.11  fof(f33,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.11    inference(flattening,[],[f32])).
% 29.63/4.11  fof(f32,plain,(
% 29.63/4.11    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.11    inference(ennf_transformation,[],[f6])).
% 29.63/4.11  fof(f6,axiom,(
% 29.63/4.11    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 29.63/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 29.63/4.11  fof(f4031,plain,(
% 29.63/4.11    ( ! [X16] : (k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | v13_lattices(sK0) | ~m1_subset_1(X16,u1_struct_0(sK0))) )),
% 29.63/4.11    inference(subsumption_resolution,[],[f4030,f2491])).
% 29.63/4.12  fof(f4030,plain,(
% 29.63/4.12    ( ! [X16] : (k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | v13_lattices(sK0) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0))) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f4029,f108])).
% 29.63/4.12  fof(f4029,plain,(
% 29.63/4.12    ( ! [X16] : (k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | v13_lattices(sK0) | ~m1_subset_1(X16,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0))) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f3987,f395])).
% 29.63/4.12  fof(f3987,plain,(
% 29.63/4.12    ( ! [X16] : (k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | v13_lattices(sK0) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0))) )),
% 29.63/4.12    inference(duplicate_literal_removal,[],[f3960])).
% 29.63/4.12  fof(f3960,plain,(
% 29.63/4.12    ( ! [X16] : (k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | v13_lattices(sK0) | k2_lattices(sK0,X16,sK2(sK0,X16)) != X16 | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK2(sK0,X16),u1_struct_0(sK0)) | ~m1_subset_1(X16,u1_struct_0(sK0))) )),
% 29.63/4.12    inference(superposition,[],[f130,f3928])).
% 29.63/4.12  fof(f3928,plain,(
% 29.63/4.12    ( ! [X10,X11] : (k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0))) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f3927,f395])).
% 29.63/4.12  fof(f3927,plain,(
% 29.63/4.12    ( ! [X10,X11] : (k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~l1_lattices(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f197,f438])).
% 29.63/4.12  fof(f438,plain,(
% 29.63/4.12    v6_lattices(sK0)),
% 29.63/4.12    inference(subsumption_resolution,[],[f437,f108])).
% 29.63/4.12  fof(f437,plain,(
% 29.63/4.12    v6_lattices(sK0) | v2_struct_0(sK0)),
% 29.63/4.12    inference(subsumption_resolution,[],[f396,f109])).
% 29.63/4.12  fof(f396,plain,(
% 29.63/4.12    v6_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 29.63/4.12    inference(resolution,[],[f111,f116])).
% 29.63/4.12  fof(f116,plain,(
% 29.63/4.12    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f31])).
% 29.63/4.12  fof(f197,plain,(
% 29.63/4.12    ( ! [X10,X11] : (k2_lattices(sK0,X10,X11) = k2_lattices(sK0,X11,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l1_lattices(sK0)) )),
% 29.63/4.12    inference(resolution,[],[f108,f131])).
% 29.63/4.12  fof(f131,plain,(
% 29.63/4.12    ( ! [X4,X0,X3] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f82])).
% 29.63/4.12  fof(f82,plain,(
% 29.63/4.12    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f79,f81,f80])).
% 29.63/4.12  fof(f80,plain,(
% 29.63/4.12    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 29.63/4.12    introduced(choice_axiom,[])).
% 29.63/4.12  fof(f81,plain,(
% 29.63/4.12    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 29.63/4.12    introduced(choice_axiom,[])).
% 29.63/4.12  fof(f79,plain,(
% 29.63/4.12    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(rectify,[],[f78])).
% 29.63/4.12  fof(f78,plain,(
% 29.63/4.12    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(nnf_transformation,[],[f41])).
% 29.63/4.12  fof(f41,plain,(
% 29.63/4.12    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(flattening,[],[f40])).
% 29.63/4.12  fof(f40,plain,(
% 29.63/4.12    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.12    inference(ennf_transformation,[],[f10])).
% 29.63/4.12  fof(f10,axiom,(
% 29.63/4.12    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 29.63/4.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 29.63/4.12  fof(f130,plain,(
% 29.63/4.12    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f77])).
% 29.63/4.12  fof(f88976,plain,(
% 29.63/4.12    ( ! [X0] : (r2_hidden(X0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 29.63/4.12    inference(resolution,[],[f9600,f1250])).
% 29.63/4.12  fof(f1250,plain,(
% 29.63/4.12    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1249,f108])).
% 29.63/4.12  fof(f1249,plain,(
% 29.63/4.12    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0)) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1248,f109])).
% 29.63/4.12  fof(f1248,plain,(
% 29.63/4.12    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1247,f110])).
% 29.63/4.12  fof(f1247,plain,(
% 29.63/4.12    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1246,f111])).
% 29.63/4.12  fof(f1246,plain,(
% 29.63/4.12    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1235,f489])).
% 29.63/4.12  fof(f489,plain,(
% 29.63/4.12    ( ! [X36] : (m1_subset_1(k15_lattice3(sK0,X36),u1_struct_0(sK0))) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f419,f108])).
% 29.63/4.12  fof(f419,plain,(
% 29.63/4.12    ( ! [X36] : (m1_subset_1(k15_lattice3(sK0,X36),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(resolution,[],[f111,f160])).
% 29.63/4.12  fof(f160,plain,(
% 29.63/4.12    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f61])).
% 29.63/4.12  fof(f61,plain,(
% 29.63/4.12    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(flattening,[],[f60])).
% 29.63/4.12  fof(f60,plain,(
% 29.63/4.12    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.12    inference(ennf_transformation,[],[f11])).
% 29.63/4.12  fof(f11,axiom,(
% 29.63/4.12    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 29.63/4.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 29.63/4.12  fof(f1235,plain,(
% 29.63/4.12    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(resolution,[],[f946,f177])).
% 29.63/4.12  fof(f177,plain,(
% 29.63/4.12    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 29.63/4.12    inference(equality_resolution,[],[f164])).
% 29.63/4.12  fof(f164,plain,(
% 29.63/4.12    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f102])).
% 29.63/4.12  fof(f102,plain,(
% 29.63/4.12    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK10(X0,X1,X2),X2) & sK10(X0,X1,X2) = X0 & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 29.63/4.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f100,f101])).
% 29.63/4.12  fof(f101,plain,(
% 29.63/4.12    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK10(X0,X1,X2),X2) & sK10(X0,X1,X2) = X0 & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))))),
% 29.63/4.12    introduced(choice_axiom,[])).
% 29.63/4.12  fof(f100,plain,(
% 29.63/4.12    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 29.63/4.12    inference(rectify,[],[f99])).
% 29.63/4.12  fof(f99,plain,(
% 29.63/4.12    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 29.63/4.12    inference(nnf_transformation,[],[f63])).
% 29.63/4.12  fof(f63,plain,(
% 29.63/4.12    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 29.63/4.12    inference(flattening,[],[f62])).
% 29.63/4.12  fof(f62,plain,(
% 29.63/4.12    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 29.63/4.12    inference(ennf_transformation,[],[f13])).
% 29.63/4.12  fof(f13,axiom,(
% 29.63/4.12    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 29.63/4.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 29.63/4.12  fof(f946,plain,(
% 29.63/4.12    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f945,f108])).
% 29.63/4.12  fof(f945,plain,(
% 29.63/4.12    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f944,f109])).
% 29.63/4.12  fof(f944,plain,(
% 29.63/4.12    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f943,f110])).
% 29.63/4.12  fof(f943,plain,(
% 29.63/4.12    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f903,f111])).
% 29.63/4.12  fof(f903,plain,(
% 29.63/4.12    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(resolution,[],[f489,f183])).
% 29.63/4.12  fof(f183,plain,(
% 29.63/4.12    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(duplicate_literal_removal,[],[f176])).
% 29.63/4.12  fof(f176,plain,(
% 29.63/4.12    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(equality_resolution,[],[f150])).
% 29.63/4.12  fof(f150,plain,(
% 29.63/4.12    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f94])).
% 29.63/4.12  fof(f94,plain,(
% 29.63/4.12    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK8(X0,X1,X2)) & r4_lattice3(X0,sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f92,f93])).
% 29.63/4.12  fof(f93,plain,(
% 29.63/4.12    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK8(X0,X1,X2)) & r4_lattice3(X0,sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 29.63/4.12    introduced(choice_axiom,[])).
% 29.63/4.12  fof(f92,plain,(
% 29.63/4.12    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(rectify,[],[f91])).
% 29.63/4.12  fof(f91,plain,(
% 29.63/4.12    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(flattening,[],[f90])).
% 29.63/4.12  fof(f90,plain,(
% 29.63/4.12    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(nnf_transformation,[],[f55])).
% 29.63/4.12  fof(f55,plain,(
% 29.63/4.12    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(flattening,[],[f54])).
% 29.63/4.12  fof(f54,plain,(
% 29.63/4.12    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.12    inference(ennf_transformation,[],[f9])).
% 29.63/4.12  fof(f9,axiom,(
% 29.63/4.12    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 29.63/4.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 29.63/4.12  fof(f9600,plain,(
% 29.63/4.12    ( ! [X0,X1] : (~r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1) | r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f9599,f108])).
% 29.63/4.12  fof(f9599,plain,(
% 29.63/4.12    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f9598,f109])).
% 29.63/4.12  fof(f9598,plain,(
% 29.63/4.12    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f9597,f110])).
% 29.63/4.12  fof(f9597,plain,(
% 29.63/4.12    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f9596,f111])).
% 29.63/4.12  fof(f9596,plain,(
% 29.63/4.12    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f9595,f489])).
% 29.63/4.12  fof(f9595,plain,(
% 29.63/4.12    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(duplicate_literal_removal,[],[f9591])).
% 29.63/4.12  fof(f9591,plain,(
% 29.63/4.12    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_6_lattice3(sK0,X1)) | ~r2_hidden(k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(resolution,[],[f9589,f178])).
% 29.63/4.12  fof(f178,plain,(
% 29.63/4.12    ( ! [X4,X2,X3,X1] : (r2_hidden(X3,a_2_6_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 29.63/4.12    inference(equality_resolution,[],[f170])).
% 29.63/4.12  fof(f170,plain,(
% 29.63/4.12    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f107])).
% 29.63/4.12  fof(f9589,plain,(
% 29.63/4.12    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 29.63/4.12    inference(resolution,[],[f1541,f113])).
% 29.63/4.12  fof(f113,plain,(
% 29.63/4.12    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f1])).
% 29.63/4.12  fof(f1,axiom,(
% 29.63/4.12    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 29.63/4.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 29.63/4.12  fof(f1541,plain,(
% 29.63/4.12    ( ! [X4,X5] : (~r1_tarski(X5,k6_domain_1(u1_struct_0(sK0),X4)) | r3_lattices(sK0,k15_lattice3(sK0,X5),X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1540,f108])).
% 29.63/4.12  fof(f1540,plain,(
% 29.63/4.12    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X5),X4) | ~r1_tarski(X5,k6_domain_1(u1_struct_0(sK0),X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1539,f109])).
% 29.63/4.12  fof(f1539,plain,(
% 29.63/4.12    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X5),X4) | ~r1_tarski(X5,k6_domain_1(u1_struct_0(sK0),X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1538,f110])).
% 29.63/4.12  fof(f1538,plain,(
% 29.63/4.12    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X5),X4) | ~r1_tarski(X5,k6_domain_1(u1_struct_0(sK0),X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1504,f111])).
% 29.63/4.12  fof(f1504,plain,(
% 29.63/4.12    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X5),X4) | ~r1_tarski(X5,k6_domain_1(u1_struct_0(sK0),X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(superposition,[],[f471,f138])).
% 29.63/4.12  fof(f138,plain,(
% 29.63/4.12    ( ! [X0,X1] : (k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f47])).
% 29.63/4.12  fof(f47,plain,(
% 29.63/4.12    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(flattening,[],[f46])).
% 29.63/4.12  fof(f46,plain,(
% 29.63/4.12    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.12    inference(ennf_transformation,[],[f17])).
% 29.63/4.12  fof(f17,axiom,(
% 29.63/4.12    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 29.63/4.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).
% 29.63/4.12  fof(f471,plain,(
% 29.63/4.12    ( ! [X15,X16] : (r3_lattices(sK0,k15_lattice3(sK0,X15),k15_lattice3(sK0,X16)) | ~r1_tarski(X15,X16)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f470,f108])).
% 29.63/4.12  fof(f470,plain,(
% 29.63/4.12    ( ! [X15,X16] : (r3_lattices(sK0,k15_lattice3(sK0,X15),k15_lattice3(sK0,X16)) | ~r1_tarski(X15,X16) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f469,f109])).
% 29.63/4.12  fof(f469,plain,(
% 29.63/4.12    ( ! [X15,X16] : (r3_lattices(sK0,k15_lattice3(sK0,X15),k15_lattice3(sK0,X16)) | ~r1_tarski(X15,X16) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f409,f110])).
% 29.63/4.12  fof(f409,plain,(
% 29.63/4.12    ( ! [X15,X16] : (r3_lattices(sK0,k15_lattice3(sK0,X15),k15_lattice3(sK0,X16)) | ~r1_tarski(X15,X16) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(resolution,[],[f111,f145])).
% 29.63/4.12  fof(f145,plain,(
% 29.63/4.12    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~r1_tarski(X1,X2) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f51])).
% 29.63/4.12  fof(f51,plain,(
% 29.63/4.12    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(flattening,[],[f50])).
% 29.63/4.12  fof(f50,plain,(
% 29.63/4.12    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.12    inference(ennf_transformation,[],[f18])).
% 29.63/4.12  fof(f18,axiom,(
% 29.63/4.12    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 29.63/4.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).
% 29.63/4.12  fof(f91270,plain,(
% 29.63/4.12    ~v13_lattices(sK0)),
% 29.63/4.12    inference(trivial_inequality_removal,[],[f90952])).
% 29.63/4.12  fof(f90952,plain,(
% 29.63/4.12    k5_lattices(sK0) != k5_lattices(sK0) | ~v13_lattices(sK0)),
% 29.63/4.12    inference(backward_demodulation,[],[f543,f90821])).
% 29.63/4.12  fof(f90821,plain,(
% 29.63/4.12    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 29.63/4.12    inference(subsumption_resolution,[],[f90820,f89124])).
% 29.63/4.12  fof(f90820,plain,(
% 29.63/4.12    ~v13_lattices(sK0) | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 29.63/4.12    inference(subsumption_resolution,[],[f90772,f558])).
% 29.63/4.12  fof(f558,plain,(
% 29.63/4.12    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 29.63/4.12    inference(subsumption_resolution,[],[f544,f108])).
% 29.63/4.12  fof(f544,plain,(
% 29.63/4.12    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 29.63/4.12    inference(resolution,[],[f395,f121])).
% 29.63/4.12  fof(f121,plain,(
% 29.63/4.12    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f35])).
% 29.63/4.12  fof(f35,plain,(
% 29.63/4.12    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(flattening,[],[f34])).
% 29.63/4.12  fof(f34,plain,(
% 29.63/4.12    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.12    inference(ennf_transformation,[],[f4])).
% 29.63/4.12  fof(f4,axiom,(
% 29.63/4.12    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 29.63/4.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 29.63/4.12  fof(f90772,plain,(
% 29.63/4.12    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 29.63/4.12    inference(resolution,[],[f89066,f6089])).
% 29.63/4.12  fof(f6089,plain,(
% 29.63/4.12    ( ! [X2] : (~r1_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0)) | ~v13_lattices(sK0) | k5_lattices(sK0) = k15_lattice3(sK0,X2)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f6088,f489])).
% 29.63/4.12  fof(f6088,plain,(
% 29.63/4.12    ( ! [X2] : (k5_lattices(sK0) = k15_lattice3(sK0,X2) | ~v13_lattices(sK0) | ~r1_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f6068,f558])).
% 29.63/4.12  fof(f6068,plain,(
% 29.63/4.12    ( ! [X2] : (k5_lattices(sK0) = k15_lattice3(sK0,X2) | ~v13_lattices(sK0) | ~r1_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))) )),
% 29.63/4.12    inference(superposition,[],[f1021,f4210])).
% 29.63/4.12  fof(f1021,plain,(
% 29.63/4.12    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X44),k5_lattices(sK0)) | ~v13_lattices(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1020,f108])).
% 29.63/4.12  fof(f1020,plain,(
% 29.63/4.12    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X44),k5_lattices(sK0)) | ~v13_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1019,f395])).
% 29.63/4.12  fof(f1019,plain,(
% 29.63/4.12    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X44),k5_lattices(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f928,f558])).
% 29.63/4.12  fof(f928,plain,(
% 29.63/4.12    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X44),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(resolution,[],[f489,f171])).
% 29.63/4.12  fof(f171,plain,(
% 29.63/4.12    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(equality_resolution,[],[f123])).
% 29.63/4.12  fof(f123,plain,(
% 29.63/4.12    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f72])).
% 29.63/4.12  fof(f72,plain,(
% 29.63/4.12    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f70,f71])).
% 29.63/4.12  fof(f71,plain,(
% 29.63/4.12    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 29.63/4.12    introduced(choice_axiom,[])).
% 29.63/4.12  fof(f70,plain,(
% 29.63/4.12    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(rectify,[],[f69])).
% 29.63/4.12  fof(f69,plain,(
% 29.63/4.12    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(nnf_transformation,[],[f37])).
% 29.63/4.12  fof(f37,plain,(
% 29.63/4.12    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(flattening,[],[f36])).
% 29.63/4.12  fof(f36,plain,(
% 29.63/4.12    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.12    inference(ennf_transformation,[],[f3])).
% 29.63/4.12  fof(f3,axiom,(
% 29.63/4.12    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 29.63/4.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 29.63/4.12  fof(f89066,plain,(
% 29.63/4.12    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 29.63/4.12    inference(resolution,[],[f88976,f8701])).
% 29.63/4.12  fof(f8701,plain,(
% 29.63/4.12    ( ! [X0,X1] : (~r2_hidden(X0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X1))) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f8700,f1644])).
% 29.63/4.12  fof(f8700,plain,(
% 29.63/4.12    ( ! [X0,X1] : (~r2_hidden(X0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f8683,f489])).
% 29.63/4.12  fof(f8683,plain,(
% 29.63/4.12    ( ! [X0,X1] : (~r2_hidden(X0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))) )),
% 29.63/4.12    inference(resolution,[],[f2430,f484])).
% 29.63/4.12  fof(f2430,plain,(
% 29.63/4.12    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X0)))) )),
% 29.63/4.12    inference(superposition,[],[f1489,f447])).
% 29.63/4.12  fof(f447,plain,(
% 29.63/4.12    ( ! [X4] : (k15_lattice3(sK0,X4) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X4))) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f446,f108])).
% 29.63/4.12  fof(f446,plain,(
% 29.63/4.12    ( ! [X4] : (k15_lattice3(sK0,X4) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X4)) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f445,f109])).
% 29.63/4.12  fof(f445,plain,(
% 29.63/4.12    ( ! [X4] : (k15_lattice3(sK0,X4) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X4)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f401,f110])).
% 29.63/4.12  fof(f401,plain,(
% 29.63/4.12    ( ! [X4] : (k15_lattice3(sK0,X4) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X4)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(resolution,[],[f111,f135])).
% 29.63/4.12  fof(f135,plain,(
% 29.63/4.12    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 29.63/4.12    inference(cnf_transformation,[],[f43])).
% 29.63/4.12  fof(f43,plain,(
% 29.63/4.12    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 29.63/4.12    inference(flattening,[],[f42])).
% 29.63/4.12  fof(f42,plain,(
% 29.63/4.12    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 29.63/4.12    inference(ennf_transformation,[],[f16])).
% 29.63/4.12  fof(f16,axiom,(
% 29.63/4.12    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 29.63/4.12    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).
% 29.63/4.12  fof(f1489,plain,(
% 29.63/4.12    ( ! [X18] : (r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18))) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1488,f108])).
% 29.63/4.12  fof(f1488,plain,(
% 29.63/4.12    ( ! [X18] : (r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18)) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1487,f109])).
% 29.63/4.12  fof(f1487,plain,(
% 29.63/4.12    ( ! [X18] : (r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1486,f110])).
% 29.63/4.12  fof(f1486,plain,(
% 29.63/4.12    ( ! [X18] : (r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1485,f111])).
% 29.63/4.12  fof(f1485,plain,(
% 29.63/4.12    ( ! [X18] : (r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(subsumption_resolution,[],[f1441,f488])).
% 29.63/4.12  fof(f1441,plain,(
% 29.63/4.12    ( ! [X18] : (~m1_subset_1(k16_lattice3(sK0,X18),u1_struct_0(sK0)) | r3_lattice3(sK0,k16_lattice3(sK0,X18),a_2_6_lattice3(sK0,X18)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 29.63/4.12    inference(superposition,[],[f174,f453])).
% 29.63/4.12  fof(f543,plain,(
% 29.63/4.12    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0)),
% 29.63/4.12    inference(subsumption_resolution,[],[f542,f108])).
% 29.63/4.12  fof(f542,plain,(
% 29.63/4.12    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | v2_struct_0(sK0)),
% 29.63/4.12    inference(subsumption_resolution,[],[f541,f109])).
% 29.63/4.12  fof(f541,plain,(
% 29.63/4.12    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 29.63/4.12    inference(subsumption_resolution,[],[f112,f111])).
% 29.63/4.12  fof(f112,plain,(
% 29.63/4.12    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 29.63/4.12    inference(cnf_transformation,[],[f67])).
% 29.63/4.12  % SZS output end Proof for theBenchmark
% 29.63/4.12  % (4447)------------------------------
% 29.63/4.12  % (4447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.63/4.12  % (4447)Termination reason: Refutation
% 29.63/4.12  
% 29.63/4.12  % (4447)Memory used [KB]: 44135
% 29.63/4.12  % (4447)Time elapsed: 3.688 s
% 29.63/4.12  % (4447)------------------------------
% 29.63/4.12  % (4447)------------------------------
% 29.63/4.12  % (4428)Success in time 3.765 s
%------------------------------------------------------------------------------
