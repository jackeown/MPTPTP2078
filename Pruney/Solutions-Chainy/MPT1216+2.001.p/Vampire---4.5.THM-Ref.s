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
% DateTime   : Thu Dec  3 13:10:44 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  364 (21265 expanded)
%              Number of leaves         :   33 (7118 expanded)
%              Depth                    :   31
%              Number of atoms          : 1130 (183732 expanded)
%              Number of equality atoms :  319 (36564 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5723,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f161,f162,f5338,f5710])).

fof(f5710,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f5700])).

fof(f5700,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f99,f168,f170,f171,f102,f103,f226,f160,f5521,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
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
    inference(nnf_transformation,[],[f74])).

fof(f74,plain,(
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
    inference(flattening,[],[f73])).

fof(f73,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f5521,plain,
    ( r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f5342,f5511])).

fof(f5511,plain,
    ( sK1 = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f1462,f5499])).

fof(f5499,plain,
    ( sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f1516,f5489])).

fof(f5489,plain,
    ( k7_lattices(sK0,sK2) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f1027,f5485])).

fof(f5485,plain,
    ( sK2 = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f812,f5472])).

fof(f5472,plain,
    ( sK2 = k2_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f850,f5468])).

fof(f5468,plain,
    ( k7_lattices(sK0,sK1) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f5349,f884])).

fof(f884,plain,(
    k7_lattices(sK0,sK1) = k3_lattices(sK0,k7_lattices(sK0,sK1),k5_lattices(sK0)) ),
    inference(backward_demodulation,[],[f563,f868])).

fof(f868,plain,(
    k5_lattices(sK0) = k7_lattices(sK0,k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f299,f867])).

fof(f867,plain,(
    k6_lattices(sK0) = k7_lattices(sK0,k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f866,f182])).

fof(f182,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattices)).

fof(f101,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,
    ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
      | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) )
    & ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
      | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f82,f85,f84,f83])).

fof(f83,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK0,X1,k7_lattices(sK0,X2))
                | k4_lattices(sK0,X1,X2) != k5_lattices(sK0) )
              & ( r3_lattices(sK0,X1,k7_lattices(sK0,X2))
                | k4_lattices(sK0,X1,X2) = k5_lattices(sK0) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r3_lattices(sK0,X1,k7_lattices(sK0,X2))
              | k4_lattices(sK0,X1,X2) != k5_lattices(sK0) )
            & ( r3_lattices(sK0,X1,k7_lattices(sK0,X2))
              | k4_lattices(sK0,X1,X2) = k5_lattices(sK0) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
            | k5_lattices(sK0) != k4_lattices(sK0,sK1,X2) )
          & ( r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
            | k5_lattices(sK0) = k4_lattices(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,
    ( ? [X2] :
        ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
          | k5_lattices(sK0) != k4_lattices(sK0,sK1,X2) )
        & ( r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
          | k5_lattices(sK0) = k4_lattices(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
        | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) )
      & ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
        | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
              & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
              & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
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

fof(f100,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f866,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k7_lattices(sK0,k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f865,f825])).

fof(f825,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(forward_demodulation,[],[f821,f183])).

fof(f183,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattices)).

fof(f821,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f188,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f188,plain,(
    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f102,f103,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f163,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f102,f107])).

fof(f107,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f865,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))) ),
    inference(forward_demodulation,[],[f760,f181])).

fof(f181,plain,(
    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(f760,plain,(
    k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f188,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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

fof(f299,plain,(
    k5_lattices(sK0) = k7_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f172,f135])).

fof(f172,plain,(
    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f163,f127])).

fof(f127,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f563,plain,(
    k7_lattices(sK0,sK1) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f480,f534])).

fof(f534,plain,(
    sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f529,f176])).

fof(f176,plain,(
    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f99,f100,f175,f102,f103,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(f175,plain,(
    v14_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f102,f99,f166,f111])).

fof(f111,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f166,plain,(
    v15_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f99,f101,f102,f114])).

fof(f114,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

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

fof(f529,plain,(
    k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f173,f150])).

fof(f173,plain,(
    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f164,f124])).

fof(f124,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f164,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f102,f108])).

fof(f108,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f480,plain,(
    k7_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f173,f138])).

fof(f5349,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k5_lattices(sK0)) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f1193,f5343])).

fof(f5343,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f241,f3784])).

fof(f3784,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f241,f155])).

fof(f155,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_1
  <=> k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f241,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f104,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f104,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f86])).

fof(f1193,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1192,f245])).

fof(f245,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f104,f150])).

fof(f1192,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1191,f1157])).

fof(f1157,plain,(
    k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1156,f860])).

fof(f860,plain,(
    k7_lattices(sK0,sK1) = k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f819,f857])).

fof(f857,plain,(
    k7_lattices(sK0,sK1) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)) ),
    inference(backward_demodulation,[],[f832,f856])).

fof(f856,plain,(
    k7_lattices(sK0,sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f765,f845])).

fof(f845,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f776,f182])).

fof(f776,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f103,f188,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f167,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f99,f100,f102,f116])).

fof(f116,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

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

fof(f765,plain,(
    k7_lattices(sK0,sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f102,f171,f103,f188,f139])).

fof(f139,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0)))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f94,f96,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0)))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
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
    inference(rectify,[],[f93])).

fof(f93,plain,(
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
    inference(nnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f832,plain,(
    k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f804,f819])).

fof(f804,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f173,f188,f149])).

fof(f819,plain,(
    k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f173,f188,f150])).

fof(f1156,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f707,f931])).

fof(f931,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,sK2,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f924,f901])).

fof(f901,plain,(
    k6_lattices(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f627,f880])).

fof(f880,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f472,f868])).

fof(f472,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k6_lattices(sK0)),k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f173,f136])).

fof(f627,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f626,f503])).

fof(f503,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k5_lattices(sK0)) = k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f172,f173,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f626,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k5_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f625,f349])).

fof(f349,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,sK2,k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f343,f214])).

fof(f214,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f99,f100,f174,f102,f104,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattices)).

fof(f174,plain,(
    v13_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f102,f99,f166,f110])).

fof(f110,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f343,plain,(
    k4_lattices(sK0,k5_lattices(sK0),sK2) = k4_lattices(sK0,sK2,k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f104,f172,f150])).

fof(f625,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK2,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f624,f506])).

fof(f506,plain,(
    k3_lattices(sK0,k6_lattices(sK0),sK2) = k3_lattices(sK0,sK2,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f173,f145])).

fof(f624,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK2,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK2),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f434,f503])).

fof(f434,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK2,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK2),k3_lattices(sK0,k6_lattices(sK0),k5_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f172,f104,f173,f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).

fof(f165,plain,(
    v11_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f99,f101,f102,f113])).

fof(f113,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f924,plain,(
    k3_lattices(sK0,sK2,k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f572,f872])).

fof(f872,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f373,f867])).

fof(f373,plain,(
    k7_lattices(sK0,k5_lattices(sK0)) = k3_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)),k7_lattices(sK0,k5_lattices(sK0))) ),
    inference(forward_demodulation,[],[f307,f353])).

fof(f353,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f338,f346])).

fof(f346,plain,(
    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f163,f174,f172,f172,f152])).

fof(f152,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK3(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK3(X0,X1)) != X1 )
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f90,f91])).

fof(f91,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK3(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK3(X0,X1)) != X1 )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
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
    inference(rectify,[],[f89])).

fof(f89,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f338,plain,(
    k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) = k4_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f172,f172,f149])).

fof(f307,plain,(
    k7_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))) = k3_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)),k7_lattices(sK0,k5_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f172,f172,f138])).

fof(f572,plain,(
    k3_lattices(sK0,sK2,k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f571,f506])).

fof(f571,plain,(
    k3_lattices(sK0,k6_lattices(sK0),sK2) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f570,f533])).

fof(f533,plain,(
    sK2 = k4_lattices(sK0,sK2,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f530,f201])).

fof(f201,plain,(
    sK2 = k4_lattices(sK0,k6_lattices(sK0),sK2) ),
    inference(unit_resulting_resolution,[],[f99,f100,f175,f102,f104,f132])).

fof(f530,plain,(
    k4_lattices(sK0,k6_lattices(sK0),sK2) = k4_lattices(sK0,sK2,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f104,f173,f150])).

fof(f570,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK2,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f467,f506])).

fof(f467,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK2,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK2),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f173,f104,f173,f133])).

fof(f707,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k6_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f104,f173,f188,f133])).

fof(f1191,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1190,f792])).

fof(f792,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f188,f145])).

fof(f1190,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f696,f182])).

fof(f696,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2),k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f103,f104,f188,f133])).

fof(f850,plain,(
    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) ),
    inference(forward_demodulation,[],[f771,f782])).

fof(f782,plain,(
    k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k1_lattices(sK0,sK2,k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f188,f144])).

fof(f771,plain,(
    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,k7_lattices(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f99,f102,f171,f104,f188,f139])).

fof(f812,plain,(
    k2_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f104,f188,f149])).

fof(f1027,plain,(
    k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1026,f822])).

fof(f822,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f104,f188,f150])).

fof(f1026,plain,(
    k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(forward_demodulation,[],[f756,f181])).

fof(f756,plain,(
    k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f188,f138])).

fof(f1516,plain,(
    sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1412,f1425])).

fof(f1425,plain,(
    k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f103,f226,f144])).

fof(f1412,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f99,f102,f171,f103,f226,f139])).

fof(f1462,plain,(
    k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f226,f149])).

fof(f5342,plain,(
    r1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK2)) ),
    inference(backward_demodulation,[],[f4488,f1462])).

fof(f4488,plain,(
    r1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK2)) ),
    inference(forward_demodulation,[],[f4481,f1524])).

fof(f1524,plain,(
    k7_lattices(sK0,sK2) = k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) ),
    inference(backward_demodulation,[],[f1459,f1522])).

fof(f1522,plain,(
    k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) ),
    inference(backward_demodulation,[],[f1486,f1521])).

fof(f1521,plain,(
    k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1407,f1508])).

fof(f1508,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(forward_demodulation,[],[f1420,f216])).

fof(f216,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f136])).

fof(f1420,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k1_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f226,f144])).

fof(f1407,plain,(
    k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,k7_lattices(sK0,sK2),sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f102,f171,f104,f226,f139])).

fof(f1486,plain,(
    k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1453,f1471])).

fof(f1471,plain,(
    k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f173,f226,f150])).

fof(f1453,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f173,f226,f149])).

fof(f1459,plain,(
    k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f173,f226,f149])).

fof(f4481,plain,(
    r1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f99,f169,f170,f171,f102,f226,f103,f173,f4467,f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f4467,plain,(
    r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f170,f171,f102,f103,f173,f540,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f540,plain,(
    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f521,f534])).

fof(f521,plain,(
    k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f173,f149])).

fof(f169,plain,(
    v7_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f99,f100,f102,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f160,plain,
    ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_2
  <=> r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f226,plain,(
    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f102,f104,f143])).

fof(f103,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f86])).

fof(f102,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f171,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f99,f100,f102,f120])).

fof(f120,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f170,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f99,f100,f102,f119])).

fof(f119,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f168,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f99,f100,f102,f117])).

fof(f117,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f5338,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f5333])).

fof(f5333,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f156,f4187])).

fof(f4187,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f4170,f217])).

fof(f217,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f137])).

fof(f4170,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f3733,f4140])).

fof(f4140,plain,
    ( k7_lattices(sK0,sK2) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f1027,f4136])).

fof(f4136,plain,
    ( sK2 = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f812,f4111])).

fof(f4111,plain,
    ( sK2 = k2_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f850,f4097])).

fof(f4097,plain,
    ( k7_lattices(sK0,sK1) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f1537,f4093])).

fof(f4093,plain,
    ( sK1 = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f1462,f4074])).

fof(f4074,plain,
    ( sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f99,f170,f171,f102,f103,f226,f1439,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f1439,plain,
    ( r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f99,f168,f170,f171,f102,f103,f159,f226,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f159,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1537,plain,(
    k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1536,f792])).

fof(f1536,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1400,f215])).

fof(f215,plain,(
    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f135])).

fof(f1400,plain,(
    k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f226,f138])).

fof(f3733,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)),sK2) ),
    inference(backward_demodulation,[],[f3709,f1852])).

fof(f1852,plain,(
    k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f1851,f245])).

fof(f1851,plain,(
    k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f1850,f1687])).

fof(f1687,plain,(
    k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1686,f1522])).

fof(f1686,plain,(
    k3_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1360,f951])).

fof(f951,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f925,f902])).

fof(f902,plain,(
    k6_lattices(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f638,f880])).

fof(f638,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f637,f503])).

fof(f637,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k5_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f636,f350])).

fof(f350,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,sK1,k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f342,f180])).

fof(f180,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f99,f100,f174,f102,f103,f134])).

fof(f342,plain,(
    k4_lattices(sK0,k5_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f172,f150])).

fof(f636,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f635,f505])).

fof(f505,plain,(
    k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f103,f173,f145])).

fof(f635,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK1),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f430,f503])).

fof(f430,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK1),k3_lattices(sK0,k6_lattices(sK0),k5_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f172,f103,f173,f133])).

fof(f925,plain,(
    k3_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f582,f872])).

fof(f582,plain,(
    k3_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f581,f505])).

fof(f581,plain,(
    k3_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f580,f534])).

fof(f580,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f463,f505])).

fof(f463,plain,(
    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK1),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f173,f103,f173,f133])).

fof(f1360,plain,(
    k3_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f103,f173,f226,f133])).

fof(f1850,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1849,f216])).

fof(f1849,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK2),k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1312,f1028])).

fof(f1028,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(backward_demodulation,[],[f864,f1027])).

fof(f864,plain,(
    k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f761,f181])).

fof(f761,plain,(
    k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f188,f138])).

fof(f1312,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK2),k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f103,f104,f226,f133])).

fof(f3709,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)),sK2) ),
    inference(backward_demodulation,[],[f3592,f2381])).

fof(f2381,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f226,f237,f145])).

fof(f237,plain,(
    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f104,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
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
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f3592,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)),sK2) ),
    inference(backward_demodulation,[],[f3554,f2450])).

fof(f2450,plain,(
    sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f2390,f1590])).

fof(f1590,plain,(
    sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f1544,f1574])).

fof(f1574,plain,(
    sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2) ),
    inference(backward_demodulation,[],[f389,f1567])).

fof(f1567,plain,(
    sK2 = k3_lattices(sK0,sK2,k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1566,f215])).

fof(f1566,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK2)) = k3_lattices(sK0,sK2,k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1565,f325])).

fof(f325,plain,(
    k3_lattices(sK0,k5_lattices(sK0),sK2) = k3_lattices(sK0,sK2,k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f172,f145])).

fof(f1565,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k5_lattices(sK0),sK2) ),
    inference(forward_demodulation,[],[f1564,f1522])).

fof(f1564,plain,(
    k3_lattices(sK0,k5_lattices(sK0),sK2) = k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1563,f868])).

fof(f1563,plain,(
    k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k6_lattices(sK0)),sK2) ),
    inference(forward_demodulation,[],[f1397,f215])).

fof(f1397,plain,(
    k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k6_lattices(sK0)),k7_lattices(sK0,k7_lattices(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f173,f226,f138])).

fof(f389,plain,(
    k3_lattices(sK0,sK2,k5_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,k5_lattices(sK0))) ),
    inference(forward_demodulation,[],[f388,f350])).

fof(f388,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,k5_lattices(sK0))) ),
    inference(forward_demodulation,[],[f290,f233])).

fof(f233,plain,(
    k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f103,f104,f145])).

fof(f290,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,k5_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f104,f103,f172,f133])).

fof(f1544,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2) ),
    inference(backward_demodulation,[],[f255,f1540])).

fof(f1540,plain,(
    sK2 = k3_lattices(sK0,sK2,sK2) ),
    inference(forward_demodulation,[],[f1539,f215])).

fof(f1539,plain,(
    k3_lattices(sK0,sK2,sK2) = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1538,f1531])).

fof(f1531,plain,(
    k7_lattices(sK0,sK2) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) ),
    inference(backward_demodulation,[],[f1461,f1530])).

fof(f1530,plain,(
    k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1402,f1513])).

fof(f1513,plain,(
    k7_lattices(sK0,sK2) = k1_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1415,f883])).

fof(f883,plain,(
    k7_lattices(sK0,sK2) = k3_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0)) ),
    inference(backward_demodulation,[],[f562,f868])).

fof(f562,plain,(
    k7_lattices(sK0,sK2) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k6_lattices(sK0))) ),
    inference(forward_demodulation,[],[f481,f533])).

fof(f481,plain,(
    k7_lattices(sK0,k4_lattices(sK0,sK2,k6_lattices(sK0))) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k6_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f173,f138])).

fof(f1415,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0)) = k1_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f172,f226,f144])).

fof(f1402,plain,(
    k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0))) ),
    inference(unit_resulting_resolution,[],[f99,f102,f171,f172,f226,f139])).

fof(f1461,plain,(
    k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f168,f163,f226,f226,f149])).

fof(f1538,plain,(
    k3_lattices(sK0,sK2,sK2) = k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1399,f215])).

fof(f1399,plain,(
    k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,k7_lattices(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f226,f226,f138])).

fof(f255,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK2)) ),
    inference(forward_demodulation,[],[f211,f233])).

fof(f211,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f104,f103,f104,f133])).

fof(f2390,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f237,f145])).

fof(f3554,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)) ),
    inference(backward_demodulation,[],[f3363,f2455])).

fof(f2455,plain,(
    k4_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f2385,f1592])).

fof(f1592,plain,(
    k4_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f1580,f245])).

fof(f1580,plain,(
    k4_lattices(sK0,sK2,sK1) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f1012,f1567])).

fof(f1012,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k5_lattices(sK0)),sK1) ),
    inference(backward_demodulation,[],[f414,f1003])).

fof(f1003,plain,(
    sK1 = k3_lattices(sK0,sK1,k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1002,f181])).

fof(f1002,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k3_lattices(sK0,sK1,k5_lattices(sK0)) ),
    inference(forward_demodulation,[],[f1001,f324])).

fof(f324,plain,(
    k3_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f103,f172,f145])).

fof(f1001,plain,(
    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(forward_demodulation,[],[f1000,f857])).

fof(f1000,plain,(
    k3_lattices(sK0,k5_lattices(sK0),sK1) = k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) ),
    inference(forward_demodulation,[],[f999,f868])).

fof(f999,plain,(
    k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k6_lattices(sK0)),sK1) ),
    inference(forward_demodulation,[],[f758,f181])).

fof(f758,plain,(
    k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k6_lattices(sK0)),k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f173,f188,f138])).

fof(f414,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k5_lattices(sK0)),k3_lattices(sK0,sK1,k5_lattices(sK0))) ),
    inference(forward_demodulation,[],[f413,f245])).

fof(f413,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k5_lattices(sK0)),k3_lattices(sK0,sK1,k5_lattices(sK0))) ),
    inference(forward_demodulation,[],[f412,f325])).

fof(f412,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k5_lattices(sK0),sK2),k3_lattices(sK0,sK1,k5_lattices(sK0))) ),
    inference(forward_demodulation,[],[f274,f324])).

fof(f274,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k5_lattices(sK0),sK2),k3_lattices(sK0,k5_lattices(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f103,f104,f172,f133])).

fof(f2385,plain,(
    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f167,f164,f172,f237,f145])).

fof(f3363,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)) ),
    inference(forward_demodulation,[],[f2217,f217])).

fof(f2217,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)) ),
    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f104,f226,f237,f133])).

fof(f156,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f154])).

fof(f162,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f105,f158,f154])).

fof(f105,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f86])).

fof(f161,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f106,f158,f154])).

fof(f106,plain,
    ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:37:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (17861)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (17850)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (17848)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (17847)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (17855)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (17845)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (17846)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (17859)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (17846)Refutation not found, incomplete strategy% (17846)------------------------------
% 0.21/0.50  % (17846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17856)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (17849)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (17865)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (17854)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (17864)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (17857)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (17863)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (17853)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (17851)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (17860)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (17865)Refutation not found, incomplete strategy% (17865)------------------------------
% 0.21/0.52  % (17865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17865)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17865)Memory used [KB]: 10618
% 0.21/0.52  % (17865)Time elapsed: 0.093 s
% 0.21/0.52  % (17865)------------------------------
% 0.21/0.52  % (17865)------------------------------
% 0.21/0.53  % (17858)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.53  % (17846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17846)Memory used [KB]: 10618
% 0.21/0.53  % (17846)Time elapsed: 0.079 s
% 0.21/0.53  % (17846)------------------------------
% 0.21/0.53  % (17846)------------------------------
% 0.21/0.53  % (17862)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.55  % (17852)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 2.26/0.66  % (17856)Refutation found. Thanks to Tanya!
% 2.26/0.66  % SZS status Theorem for theBenchmark
% 2.26/0.66  % SZS output start Proof for theBenchmark
% 2.26/0.66  fof(f5723,plain,(
% 2.26/0.66    $false),
% 2.26/0.66    inference(avatar_sat_refutation,[],[f161,f162,f5338,f5710])).
% 2.26/0.66  fof(f5710,plain,(
% 2.26/0.66    ~spl6_1 | spl6_2),
% 2.26/0.66    inference(avatar_contradiction_clause,[],[f5700])).
% 2.26/0.66  fof(f5700,plain,(
% 2.26/0.66    $false | (~spl6_1 | spl6_2)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f170,f171,f102,f103,f226,f160,f5521,f147])).
% 2.26/0.66  fof(f147,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f98])).
% 2.26/0.66  fof(f98,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(nnf_transformation,[],[f74])).
% 2.26/0.66  fof(f74,plain,(
% 2.26/0.66    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f73])).
% 2.26/0.66  fof(f73,plain,(
% 2.26/0.66    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f16])).
% 2.26/0.66  fof(f16,axiom,(
% 2.26/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 2.26/0.66  fof(f5521,plain,(
% 2.26/0.66    r1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl6_1),
% 2.26/0.66    inference(backward_demodulation,[],[f5342,f5511])).
% 2.26/0.66  fof(f5511,plain,(
% 2.26/0.66    sK1 = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl6_1),
% 2.26/0.66    inference(backward_demodulation,[],[f1462,f5499])).
% 2.26/0.66  fof(f5499,plain,(
% 2.26/0.66    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl6_1),
% 2.26/0.66    inference(backward_demodulation,[],[f1516,f5489])).
% 2.26/0.66  fof(f5489,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl6_1),
% 2.26/0.66    inference(backward_demodulation,[],[f1027,f5485])).
% 2.26/0.66  fof(f5485,plain,(
% 2.26/0.66    sK2 = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)) | ~spl6_1),
% 2.26/0.66    inference(backward_demodulation,[],[f812,f5472])).
% 2.26/0.66  fof(f5472,plain,(
% 2.26/0.66    sK2 = k2_lattices(sK0,sK2,k7_lattices(sK0,sK1)) | ~spl6_1),
% 2.26/0.66    inference(backward_demodulation,[],[f850,f5468])).
% 2.26/0.66  fof(f5468,plain,(
% 2.26/0.66    k7_lattices(sK0,sK1) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) | ~spl6_1),
% 2.26/0.66    inference(forward_demodulation,[],[f5349,f884])).
% 2.26/0.66  fof(f884,plain,(
% 2.26/0.66    k7_lattices(sK0,sK1) = k3_lattices(sK0,k7_lattices(sK0,sK1),k5_lattices(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f563,f868])).
% 2.26/0.66  fof(f868,plain,(
% 2.26/0.66    k5_lattices(sK0) = k7_lattices(sK0,k6_lattices(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f299,f867])).
% 2.26/0.66  fof(f867,plain,(
% 2.26/0.66    k6_lattices(sK0) = k7_lattices(sK0,k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f866,f182])).
% 2.26/0.66  fof(f182,plain,(
% 2.26/0.66    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f136])).
% 2.26/0.66  fof(f136,plain,(
% 2.26/0.66    ( ! [X0,X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f60])).
% 2.26/0.66  fof(f60,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f59])).
% 2.26/0.66  fof(f59,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f23])).
% 2.26/0.66  fof(f23,axiom,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattices)).
% 2.26/0.66  fof(f101,plain,(
% 2.26/0.66    v17_lattices(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f86])).
% 2.26/0.66  fof(f86,plain,(
% 2.26/0.66    (((~r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2)) & (r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 2.26/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f82,f85,f84,f83])).
% 2.26/0.66  fof(f83,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_lattices(sK0,X1,k7_lattices(sK0,X2)) | k4_lattices(sK0,X1,X2) != k5_lattices(sK0)) & (r3_lattices(sK0,X1,k7_lattices(sK0,X2)) | k4_lattices(sK0,X1,X2) = k5_lattices(sK0)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 2.26/0.66    introduced(choice_axiom,[])).
% 2.26/0.66  fof(f84,plain,(
% 2.26/0.66    ? [X1] : (? [X2] : ((~r3_lattices(sK0,X1,k7_lattices(sK0,X2)) | k4_lattices(sK0,X1,X2) != k5_lattices(sK0)) & (r3_lattices(sK0,X1,k7_lattices(sK0,X2)) | k4_lattices(sK0,X1,X2) = k5_lattices(sK0)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r3_lattices(sK0,sK1,k7_lattices(sK0,X2)) | k5_lattices(sK0) != k4_lattices(sK0,sK1,X2)) & (r3_lattices(sK0,sK1,k7_lattices(sK0,X2)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 2.26/0.66    introduced(choice_axiom,[])).
% 2.26/0.66  fof(f85,plain,(
% 2.26/0.66    ? [X2] : ((~r3_lattices(sK0,sK1,k7_lattices(sK0,X2)) | k5_lattices(sK0) != k4_lattices(sK0,sK1,X2)) & (r3_lattices(sK0,sK1,k7_lattices(sK0,X2)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2)) & (r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 2.26/0.66    introduced(choice_axiom,[])).
% 2.26/0.66  fof(f82,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f81])).
% 2.26/0.66  fof(f81,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : (? [X2] : (((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.26/0.66    inference(nnf_transformation,[],[f31])).
% 2.26/0.66  fof(f31,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : (? [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <~> r3_lattices(X0,X1,k7_lattices(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f30])).
% 2.26/0.66  fof(f30,plain,(
% 2.26/0.66    ? [X0] : (? [X1] : (? [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <~> r3_lattices(X0,X1,k7_lattices(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f27])).
% 2.26/0.66  fof(f27,negated_conjecture,(
% 2.26/0.66    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))))))),
% 2.26/0.66    inference(negated_conjecture,[],[f26])).
% 2.26/0.66  fof(f26,conjecture,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).
% 2.26/0.66  fof(f100,plain,(
% 2.26/0.66    v10_lattices(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f86])).
% 2.26/0.66  fof(f866,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k7_lattices(sK0,k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f865,f825])).
% 2.26/0.66  fof(f825,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))),
% 2.26/0.66    inference(forward_demodulation,[],[f821,f183])).
% 2.26/0.66  fof(f183,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f137])).
% 2.26/0.66  fof(f137,plain,(
% 2.26/0.66    ( ! [X0,X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f62])).
% 2.26/0.66  fof(f62,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f61])).
% 2.26/0.66  fof(f61,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f22])).
% 2.26/0.66  fof(f22,axiom,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattices)).
% 2.26/0.66  fof(f821,plain,(
% 2.26/0.66    k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f188,f150])).
% 2.26/0.66  fof(f150,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f80])).
% 2.26/0.66  fof(f80,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f79])).
% 2.26/0.66  fof(f79,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f5])).
% 2.26/0.66  fof(f5,axiom,(
% 2.26/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 2.26/0.66  fof(f188,plain,(
% 2.26/0.66    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f102,f103,f143])).
% 2.26/0.66  fof(f143,plain,(
% 2.26/0.66    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f68])).
% 2.26/0.66  fof(f68,plain,(
% 2.26/0.66    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f67])).
% 2.26/0.66  fof(f67,plain,(
% 2.26/0.66    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f12])).
% 2.26/0.66  fof(f12,axiom,(
% 2.26/0.66    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).
% 2.26/0.66  fof(f163,plain,(
% 2.26/0.66    l1_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f102,f107])).
% 2.26/0.66  fof(f107,plain,(
% 2.26/0.66    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f32])).
% 2.26/0.66  fof(f32,plain,(
% 2.26/0.66    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f13])).
% 2.26/0.66  fof(f13,axiom,(
% 2.26/0.66    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 2.26/0.66  fof(f865,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK1)))),
% 2.26/0.66    inference(forward_demodulation,[],[f760,f181])).
% 2.26/0.66  fof(f181,plain,(
% 2.26/0.66    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f135])).
% 2.26/0.66  fof(f135,plain,(
% 2.26/0.66    ( ! [X0,X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f58])).
% 2.26/0.66  fof(f58,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f57])).
% 2.26/0.66  fof(f57,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f24])).
% 2.26/0.66  fof(f24,axiom,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).
% 2.26/0.66  fof(f760,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f188,f138])).
% 2.26/0.66  fof(f138,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f64])).
% 2.26/0.66  fof(f64,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f63])).
% 2.26/0.66  fof(f63,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f25])).
% 2.26/0.66  fof(f25,axiom,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattices)).
% 2.26/0.66  fof(f299,plain,(
% 2.26/0.66    k5_lattices(sK0) = k7_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f172,f135])).
% 2.26/0.66  fof(f172,plain,(
% 2.26/0.66    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f163,f127])).
% 2.26/0.66  fof(f127,plain,(
% 2.26/0.66    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f48])).
% 2.26/0.66  fof(f48,plain,(
% 2.26/0.66    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f47])).
% 2.26/0.66  fof(f47,plain,(
% 2.26/0.66    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f10])).
% 2.26/0.66  fof(f10,axiom,(
% 2.26/0.66    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 2.26/0.66  fof(f563,plain,(
% 2.26/0.66    k7_lattices(sK0,sK1) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f480,f534])).
% 2.26/0.66  fof(f534,plain,(
% 2.26/0.66    sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f529,f176])).
% 2.26/0.66  fof(f176,plain,(
% 2.26/0.66    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f175,f102,f103,f132])).
% 2.26/0.66  fof(f132,plain,(
% 2.26/0.66    ( ! [X0,X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f52])).
% 2.26/0.66  fof(f52,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f51])).
% 2.26/0.66  fof(f51,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f21])).
% 2.26/0.66  fof(f21,axiom,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).
% 2.26/0.66  fof(f175,plain,(
% 2.26/0.66    v14_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f102,f99,f166,f111])).
% 2.26/0.66  fof(f111,plain,(
% 2.26/0.66    ( ! [X0] : (v14_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f34])).
% 2.26/0.66  fof(f34,plain,(
% 2.26/0.66    ! [X0] : ((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.26/0.66    inference(flattening,[],[f33])).
% 2.26/0.66  fof(f33,plain,(
% 2.26/0.66    ! [X0] : (((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | (~v15_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f2])).
% 2.26/0.66  fof(f2,axiom,(
% 2.26/0.66    ! [X0] : (l3_lattices(X0) => ((v15_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).
% 2.26/0.66  fof(f166,plain,(
% 2.26/0.66    v15_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f101,f102,f114])).
% 2.26/0.66  fof(f114,plain,(
% 2.26/0.66    ( ! [X0] : (v15_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f36])).
% 2.26/0.66  fof(f36,plain,(
% 2.26/0.66    ! [X0] : ((v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.26/0.66    inference(flattening,[],[f35])).
% 2.26/0.66  fof(f35,plain,(
% 2.26/0.66    ! [X0] : (((v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f28])).
% 2.26/0.66  fof(f28,plain,(
% 2.26/0.66    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 2.26/0.66    inference(pure_predicate_removal,[],[f3])).
% 2.26/0.66  fof(f3,axiom,(
% 2.26/0.66    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).
% 2.26/0.66  fof(f529,plain,(
% 2.26/0.66    k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f173,f150])).
% 2.26/0.66  fof(f173,plain,(
% 2.26/0.66    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f164,f124])).
% 2.26/0.66  fof(f124,plain,(
% 2.26/0.66    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f44])).
% 2.26/0.66  fof(f44,plain,(
% 2.26/0.66    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f43])).
% 2.26/0.66  fof(f43,plain,(
% 2.26/0.66    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f11])).
% 2.26/0.66  fof(f11,axiom,(
% 2.26/0.66    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).
% 2.26/0.66  fof(f164,plain,(
% 2.26/0.66    l2_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f102,f108])).
% 2.26/0.66  fof(f108,plain,(
% 2.26/0.66    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f32])).
% 2.26/0.66  fof(f480,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f173,f138])).
% 2.26/0.66  fof(f5349,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),k5_lattices(sK0)) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) | ~spl6_1),
% 2.26/0.66    inference(backward_demodulation,[],[f1193,f5343])).
% 2.26/0.66  fof(f5343,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) | ~spl6_1),
% 2.26/0.66    inference(backward_demodulation,[],[f241,f3784])).
% 2.26/0.66  fof(f3784,plain,(
% 2.26/0.66    k5_lattices(sK0) = k2_lattices(sK0,sK1,sK2) | ~spl6_1),
% 2.26/0.66    inference(backward_demodulation,[],[f241,f155])).
% 2.26/0.66  fof(f155,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) | ~spl6_1),
% 2.26/0.66    inference(avatar_component_clause,[],[f154])).
% 2.26/0.66  fof(f154,plain,(
% 2.26/0.66    spl6_1 <=> k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)),
% 2.26/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.26/0.66  fof(f241,plain,(
% 2.26/0.66    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f104,f149])).
% 2.26/0.66  fof(f149,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f78])).
% 2.26/0.66  fof(f78,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f77])).
% 2.26/0.66  fof(f77,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f15])).
% 2.26/0.66  fof(f15,axiom,(
% 2.26/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 2.26/0.66  fof(f104,plain,(
% 2.26/0.66    m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.26/0.66    inference(cnf_transformation,[],[f86])).
% 2.26/0.66  fof(f1193,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))),
% 2.26/0.66    inference(forward_demodulation,[],[f1192,f245])).
% 2.26/0.66  fof(f245,plain,(
% 2.26/0.66    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f104,f150])).
% 2.26/0.66  fof(f1192,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))),
% 2.26/0.66    inference(forward_demodulation,[],[f1191,f1157])).
% 2.26/0.66  fof(f1157,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f1156,f860])).
% 2.26/0.66  fof(f860,plain,(
% 2.26/0.66    k7_lattices(sK0,sK1) = k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f819,f857])).
% 2.26/0.66  fof(f857,plain,(
% 2.26/0.66    k7_lattices(sK0,sK1) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))),
% 2.26/0.66    inference(backward_demodulation,[],[f832,f856])).
% 2.26/0.66  fof(f856,plain,(
% 2.26/0.66    k7_lattices(sK0,sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f765,f845])).
% 2.26/0.66  fof(f845,plain,(
% 2.26/0.66    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 2.26/0.66    inference(forward_demodulation,[],[f776,f182])).
% 2.26/0.66  fof(f776,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f103,f188,f144])).
% 2.26/0.66  fof(f144,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f70])).
% 2.26/0.66  fof(f70,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f69])).
% 2.26/0.66  fof(f69,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f14])).
% 2.26/0.66  fof(f14,axiom,(
% 2.26/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 2.26/0.66  fof(f167,plain,(
% 2.26/0.66    v4_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f102,f116])).
% 2.26/0.66  fof(f116,plain,(
% 2.26/0.66    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f38])).
% 2.26/0.66  fof(f38,plain,(
% 2.26/0.66    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.26/0.66    inference(flattening,[],[f37])).
% 2.26/0.66  fof(f37,plain,(
% 2.26/0.66    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.26/0.66    inference(ennf_transformation,[],[f29])).
% 2.26/0.66  fof(f29,plain,(
% 2.26/0.66    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.26/0.66    inference(pure_predicate_removal,[],[f1])).
% 2.26/0.66  fof(f1,axiom,(
% 2.26/0.66    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 2.26/0.66  fof(f765,plain,(
% 2.26/0.66    k7_lattices(sK0,sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),k1_lattices(sK0,k7_lattices(sK0,sK1),sK1))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f102,f171,f103,f188,f139])).
% 2.26/0.66  fof(f139,plain,(
% 2.26/0.66    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f97])).
% 2.26/0.66  fof(f97,plain,(
% 2.26/0.66    ! [X0] : (((v9_lattices(X0) | ((sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f94,f96,f95])).
% 2.26/0.66  fof(f95,plain,(
% 2.26/0.66    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 2.26/0.66    introduced(choice_axiom,[])).
% 2.26/0.66  fof(f96,plain,(
% 2.26/0.66    ! [X0] : (? [X2] : (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 2.26/0.66    introduced(choice_axiom,[])).
% 2.26/0.66  fof(f94,plain,(
% 2.26/0.66    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(rectify,[],[f93])).
% 2.26/0.66  fof(f93,plain,(
% 2.26/0.66    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(nnf_transformation,[],[f66])).
% 2.26/0.66  fof(f66,plain,(
% 2.26/0.66    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f65])).
% 2.26/0.66  fof(f65,plain,(
% 2.26/0.66    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f8])).
% 2.26/0.66  fof(f8,axiom,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 2.26/0.66  fof(f832,plain,(
% 2.26/0.66    k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f804,f819])).
% 2.26/0.66  fof(f804,plain,(
% 2.26/0.66    k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f173,f188,f149])).
% 2.26/0.66  fof(f819,plain,(
% 2.26/0.66    k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f173,f188,f150])).
% 2.26/0.66  fof(f1156,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f707,f931])).
% 2.26/0.66  fof(f931,plain,(
% 2.26/0.66    k6_lattices(sK0) = k3_lattices(sK0,sK2,k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f924,f901])).
% 2.26/0.66  fof(f901,plain,(
% 2.26/0.66    k6_lattices(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k6_lattices(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f627,f880])).
% 2.26/0.66  fof(f880,plain,(
% 2.26/0.66    k6_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f472,f868])).
% 2.26/0.66  fof(f472,plain,(
% 2.26/0.66    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,k6_lattices(sK0)),k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f173,f136])).
% 2.26/0.66  fof(f627,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f626,f503])).
% 2.26/0.66  fof(f503,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k5_lattices(sK0)) = k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f172,f173,f145])).
% 2.26/0.66  fof(f145,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f72])).
% 2.26/0.66  fof(f72,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f71])).
% 2.26/0.66  fof(f71,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f4])).
% 2.26/0.66  fof(f4,axiom,(
% 2.26/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 2.26/0.66  fof(f626,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k5_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f625,f349])).
% 2.26/0.66  fof(f349,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,sK2,k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f343,f214])).
% 2.26/0.66  fof(f214,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK2)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f174,f102,f104,f134])).
% 2.26/0.66  fof(f134,plain,(
% 2.26/0.66    ( ! [X0,X1] : (k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f56])).
% 2.26/0.66  fof(f56,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f55])).
% 2.26/0.66  fof(f55,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f20])).
% 2.26/0.66  fof(f20,axiom,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattices)).
% 2.26/0.66  fof(f174,plain,(
% 2.26/0.66    v13_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f102,f99,f166,f110])).
% 2.26/0.66  fof(f110,plain,(
% 2.26/0.66    ( ! [X0] : (v13_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f34])).
% 2.26/0.66  fof(f343,plain,(
% 2.26/0.66    k4_lattices(sK0,k5_lattices(sK0),sK2) = k4_lattices(sK0,sK2,k5_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f104,f172,f150])).
% 2.26/0.66  fof(f625,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK2,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f624,f506])).
% 2.26/0.66  fof(f506,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),sK2) = k3_lattices(sK0,sK2,k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f173,f145])).
% 2.26/0.66  fof(f624,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK2,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK2),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f434,f503])).
% 2.26/0.66  fof(f434,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK2,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK2),k3_lattices(sK0,k6_lattices(sK0),k5_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f172,f104,f173,f133])).
% 2.26/0.66  fof(f133,plain,(
% 2.26/0.66    ( ! [X2,X0,X3,X1] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f54])).
% 2.26/0.66  fof(f54,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f53])).
% 2.26/0.66  fof(f53,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f19])).
% 2.26/0.66  fof(f19,axiom,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).
% 2.26/0.66  fof(f165,plain,(
% 2.26/0.66    v11_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f101,f102,f113])).
% 2.26/0.66  fof(f113,plain,(
% 2.26/0.66    ( ! [X0] : (v11_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f36])).
% 2.26/0.66  fof(f924,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k6_lattices(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f572,f872])).
% 2.26/0.66  fof(f872,plain,(
% 2.26/0.66    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f373,f867])).
% 2.26/0.66  fof(f373,plain,(
% 2.26/0.66    k7_lattices(sK0,k5_lattices(sK0)) = k3_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)),k7_lattices(sK0,k5_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f307,f353])).
% 2.26/0.66  fof(f353,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f338,f346])).
% 2.26/0.66  fof(f346,plain,(
% 2.26/0.66    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f163,f174,f172,f172,f152])).
% 2.26/0.66  fof(f152,plain,(
% 2.26/0.66    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(equality_resolution,[],[f128])).
% 2.26/0.66  fof(f128,plain,(
% 2.26/0.66    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f92])).
% 2.26/0.66  fof(f92,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f90,f91])).
% 2.26/0.66  fof(f91,plain,(
% 2.26/0.66    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 2.26/0.66    introduced(choice_axiom,[])).
% 2.26/0.66  fof(f90,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(rectify,[],[f89])).
% 2.26/0.66  fof(f89,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(nnf_transformation,[],[f50])).
% 2.26/0.66  fof(f50,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f49])).
% 2.26/0.66  fof(f49,plain,(
% 2.26/0.66    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f6])).
% 2.26/0.66  fof(f6,axiom,(
% 2.26/0.66    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 2.26/0.66  fof(f338,plain,(
% 2.26/0.66    k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) = k4_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f172,f172,f149])).
% 2.26/0.66  fof(f307,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))) = k3_lattices(sK0,k7_lattices(sK0,k5_lattices(sK0)),k7_lattices(sK0,k5_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f172,f172,f138])).
% 2.26/0.66  fof(f572,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f571,f506])).
% 2.26/0.66  fof(f571,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),sK2) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f570,f533])).
% 2.26/0.66  fof(f533,plain,(
% 2.26/0.66    sK2 = k4_lattices(sK0,sK2,k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f530,f201])).
% 2.26/0.66  fof(f201,plain,(
% 2.26/0.66    sK2 = k4_lattices(sK0,k6_lattices(sK0),sK2)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f175,f102,f104,f132])).
% 2.26/0.66  fof(f530,plain,(
% 2.26/0.66    k4_lattices(sK0,k6_lattices(sK0),sK2) = k4_lattices(sK0,sK2,k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f104,f173,f150])).
% 2.26/0.66  fof(f570,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK2,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f467,f506])).
% 2.26/0.66  fof(f467,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK2,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK2),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f173,f104,f173,f133])).
% 2.26/0.66  fof(f707,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k6_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f104,f173,f188,f133])).
% 2.26/0.66  fof(f1191,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f1190,f792])).
% 2.26/0.66  fof(f792,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f188,f145])).
% 2.26/0.66  fof(f1190,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2),k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f696,f182])).
% 2.26/0.66  fof(f696,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2),k3_lattices(sK0,k7_lattices(sK0,sK1),sK1))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f103,f104,f188,f133])).
% 2.26/0.66  fof(f850,plain,(
% 2.26/0.66    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))),
% 2.26/0.66    inference(forward_demodulation,[],[f771,f782])).
% 2.26/0.66  fof(f782,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k1_lattices(sK0,sK2,k7_lattices(sK0,sK1))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f188,f144])).
% 2.26/0.66  fof(f771,plain,(
% 2.26/0.66    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,k7_lattices(sK0,sK1)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f102,f171,f104,f188,f139])).
% 2.26/0.66  fof(f812,plain,(
% 2.26/0.66    k2_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f104,f188,f149])).
% 2.26/0.66  fof(f1027,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(forward_demodulation,[],[f1026,f822])).
% 2.26/0.66  fof(f822,plain,(
% 2.26/0.66    k4_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f104,f188,f150])).
% 2.26/0.66  fof(f1026,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(forward_demodulation,[],[f756,f181])).
% 2.26/0.66  fof(f756,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f188,f138])).
% 2.26/0.66  fof(f1516,plain,(
% 2.26/0.66    sK1 = k2_lattices(sK0,sK1,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(forward_demodulation,[],[f1412,f1425])).
% 2.26/0.66  fof(f1425,plain,(
% 2.26/0.66    k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f103,f226,f144])).
% 2.26/0.66  fof(f1412,plain,(
% 2.26/0.66    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f102,f171,f103,f226,f139])).
% 2.26/0.66  fof(f1462,plain,(
% 2.26/0.66    k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f226,f149])).
% 2.26/0.66  fof(f5342,plain,(
% 2.26/0.66    r1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(backward_demodulation,[],[f4488,f1462])).
% 2.26/0.66  fof(f4488,plain,(
% 2.26/0.66    r1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(forward_demodulation,[],[f4481,f1524])).
% 2.26/0.66  fof(f1524,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(backward_demodulation,[],[f1459,f1522])).
% 2.26/0.66  fof(f1522,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(backward_demodulation,[],[f1486,f1521])).
% 2.26/0.66  fof(f1521,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f1407,f1508])).
% 2.26/0.66  fof(f1508,plain,(
% 2.26/0.66    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK2),sK2)),
% 2.26/0.66    inference(forward_demodulation,[],[f1420,f216])).
% 2.26/0.66  fof(f216,plain,(
% 2.26/0.66    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f136])).
% 2.26/0.66  fof(f1420,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k1_lattices(sK0,k7_lattices(sK0,sK2),sK2)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f226,f144])).
% 2.26/0.66  fof(f1407,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,k7_lattices(sK0,sK2),sK2))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f102,f171,f104,f226,f139])).
% 2.26/0.66  fof(f1486,plain,(
% 2.26/0.66    k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f1453,f1471])).
% 2.26/0.66  fof(f1471,plain,(
% 2.26/0.66    k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f173,f226,f150])).
% 2.26/0.66  fof(f1453,plain,(
% 2.26/0.66    k4_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f173,f226,f149])).
% 2.26/0.66  fof(f1459,plain,(
% 2.26/0.66    k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f173,f226,f149])).
% 2.26/0.66  fof(f4481,plain,(
% 2.26/0.66    r1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f169,f170,f171,f102,f226,f103,f173,f4467,f121])).
% 2.26/0.66  fof(f121,plain,(
% 2.26/0.66    ( ! [X2,X0,X3,X1] : (r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f40])).
% 2.26/0.66  fof(f40,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f39])).
% 2.26/0.66  fof(f39,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) | ~r1_lattices(X0,X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v7_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f18])).
% 2.26/0.66  fof(f18,axiom,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).
% 2.26/0.66  fof(f4467,plain,(
% 2.26/0.66    r1_lattices(sK0,sK1,k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f170,f171,f102,f103,f173,f540,f123])).
% 2.26/0.66  fof(f123,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f87])).
% 2.26/0.66  fof(f87,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(nnf_transformation,[],[f42])).
% 2.26/0.66  fof(f42,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f41])).
% 2.26/0.66  fof(f41,plain,(
% 2.26/0.66    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f17])).
% 2.26/0.66  fof(f17,axiom,(
% 2.26/0.66    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 2.26/0.66  fof(f540,plain,(
% 2.26/0.66    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f521,f534])).
% 2.26/0.66  fof(f521,plain,(
% 2.26/0.66    k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f173,f149])).
% 2.26/0.66  fof(f169,plain,(
% 2.26/0.66    v7_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f102,f118])).
% 2.26/0.66  fof(f118,plain,(
% 2.26/0.66    ( ! [X0] : (v7_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f38])).
% 2.26/0.66  fof(f160,plain,(
% 2.26/0.66    ~r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | spl6_2),
% 2.26/0.66    inference(avatar_component_clause,[],[f158])).
% 2.26/0.66  fof(f158,plain,(
% 2.26/0.66    spl6_2 <=> r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 2.26/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.26/0.66  fof(f226,plain,(
% 2.26/0.66    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f102,f104,f143])).
% 2.26/0.66  fof(f103,plain,(
% 2.26/0.66    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.26/0.66    inference(cnf_transformation,[],[f86])).
% 2.26/0.66  fof(f102,plain,(
% 2.26/0.66    l3_lattices(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f86])).
% 2.26/0.66  fof(f171,plain,(
% 2.26/0.66    v9_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f102,f120])).
% 2.26/0.66  fof(f120,plain,(
% 2.26/0.66    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f38])).
% 2.26/0.66  fof(f170,plain,(
% 2.26/0.66    v8_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f102,f119])).
% 2.26/0.66  fof(f119,plain,(
% 2.26/0.66    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f38])).
% 2.26/0.66  fof(f168,plain,(
% 2.26/0.66    v6_lattices(sK0)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f102,f117])).
% 2.26/0.66  fof(f117,plain,(
% 2.26/0.66    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f38])).
% 2.26/0.66  fof(f99,plain,(
% 2.26/0.66    ~v2_struct_0(sK0)),
% 2.26/0.66    inference(cnf_transformation,[],[f86])).
% 2.26/0.66  fof(f5338,plain,(
% 2.26/0.66    spl6_1 | ~spl6_2),
% 2.26/0.66    inference(avatar_contradiction_clause,[],[f5333])).
% 2.26/0.66  fof(f5333,plain,(
% 2.26/0.66    $false | (spl6_1 | ~spl6_2)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f156,f4187])).
% 2.26/0.66  fof(f4187,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) | ~spl6_2),
% 2.26/0.66    inference(forward_demodulation,[],[f4170,f217])).
% 2.26/0.66  fof(f217,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f137])).
% 2.26/0.66  fof(f4170,plain,(
% 2.26/0.66    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) | ~spl6_2),
% 2.26/0.66    inference(backward_demodulation,[],[f3733,f4140])).
% 2.26/0.66  fof(f4140,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl6_2),
% 2.26/0.66    inference(backward_demodulation,[],[f1027,f4136])).
% 2.26/0.66  fof(f4136,plain,(
% 2.26/0.66    sK2 = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)) | ~spl6_2),
% 2.26/0.66    inference(backward_demodulation,[],[f812,f4111])).
% 2.26/0.66  fof(f4111,plain,(
% 2.26/0.66    sK2 = k2_lattices(sK0,sK2,k7_lattices(sK0,sK1)) | ~spl6_2),
% 2.26/0.66    inference(backward_demodulation,[],[f850,f4097])).
% 2.26/0.66  fof(f4097,plain,(
% 2.26/0.66    k7_lattices(sK0,sK1) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) | ~spl6_2),
% 2.26/0.66    inference(backward_demodulation,[],[f1537,f4093])).
% 2.26/0.66  fof(f4093,plain,(
% 2.26/0.66    sK1 = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl6_2),
% 2.26/0.66    inference(backward_demodulation,[],[f1462,f4074])).
% 2.26/0.66  fof(f4074,plain,(
% 2.26/0.66    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl6_2),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f170,f171,f102,f103,f226,f1439,f122])).
% 2.26/0.66  fof(f122,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f87])).
% 2.26/0.66  fof(f1439,plain,(
% 2.26/0.66    r1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl6_2),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f170,f171,f102,f103,f159,f226,f146])).
% 2.26/0.66  fof(f146,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f98])).
% 2.26/0.66  fof(f159,plain,(
% 2.26/0.66    r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl6_2),
% 2.26/0.66    inference(avatar_component_clause,[],[f158])).
% 2.26/0.66  fof(f1537,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(forward_demodulation,[],[f1536,f792])).
% 2.26/0.66  fof(f1536,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(forward_demodulation,[],[f1400,f215])).
% 2.26/0.66  fof(f215,plain,(
% 2.26/0.66    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f135])).
% 2.26/0.66  fof(f1400,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f103,f226,f138])).
% 2.26/0.66  fof(f3733,plain,(
% 2.26/0.66    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)),sK2)),
% 2.26/0.66    inference(backward_demodulation,[],[f3709,f1852])).
% 2.26/0.66  fof(f1852,plain,(
% 2.26/0.66    k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2))),
% 2.26/0.66    inference(forward_demodulation,[],[f1851,f245])).
% 2.26/0.66  fof(f1851,plain,(
% 2.26/0.66    k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,sK1))),
% 2.26/0.66    inference(forward_demodulation,[],[f1850,f1687])).
% 2.26/0.66  fof(f1687,plain,(
% 2.26/0.66    k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(forward_demodulation,[],[f1686,f1522])).
% 2.26/0.66  fof(f1686,plain,(
% 2.26/0.66    k3_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(forward_demodulation,[],[f1360,f951])).
% 2.26/0.66  fof(f951,plain,(
% 2.26/0.66    k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f925,f902])).
% 2.26/0.66  fof(f902,plain,(
% 2.26/0.66    k6_lattices(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f638,f880])).
% 2.26/0.66  fof(f638,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f637,f503])).
% 2.26/0.66  fof(f637,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k5_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f636,f350])).
% 2.26/0.66  fof(f350,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,sK1,k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f342,f180])).
% 2.26/0.66  fof(f180,plain,(
% 2.26/0.66    k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK1)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f174,f102,f103,f134])).
% 2.26/0.66  fof(f342,plain,(
% 2.26/0.66    k4_lattices(sK0,k5_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k5_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f172,f150])).
% 2.26/0.66  fof(f636,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f635,f505])).
% 2.26/0.66  fof(f505,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f103,f173,f145])).
% 2.26/0.66  fof(f635,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK1),k3_lattices(sK0,k5_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f430,f503])).
% 2.26/0.66  fof(f430,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK1),k3_lattices(sK0,k6_lattices(sK0),k5_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f172,f103,f173,f133])).
% 2.26/0.66  fof(f925,plain,(
% 2.26/0.66    k3_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f582,f872])).
% 2.26/0.66  fof(f582,plain,(
% 2.26/0.66    k3_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f581,f505])).
% 2.26/0.66  fof(f581,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f580,f534])).
% 2.26/0.66  fof(f580,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f463,f505])).
% 2.26/0.66  fof(f463,plain,(
% 2.26/0.66    k3_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k6_lattices(sK0),sK1),k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f173,f103,f173,f133])).
% 2.26/0.66  fof(f1360,plain,(
% 2.26/0.66    k3_lattices(sK0,sK1,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))) = k4_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0)),k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f103,f173,f226,f133])).
% 2.26/0.66  fof(f1850,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k6_lattices(sK0),k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(forward_demodulation,[],[f1849,f216])).
% 2.26/0.66  fof(f1849,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK2),k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(forward_demodulation,[],[f1312,f1028])).
% 2.26/0.66  fof(f1028,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(backward_demodulation,[],[f864,f1027])).
% 2.26/0.66  fof(f864,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)),
% 2.26/0.66    inference(forward_demodulation,[],[f761,f181])).
% 2.26/0.66  fof(f761,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f188,f138])).
% 2.26/0.66  fof(f1312,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK2),k3_lattices(sK0,k7_lattices(sK0,sK2),sK1))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f103,f104,f226,f133])).
% 2.26/0.66  fof(f3709,plain,(
% 2.26/0.66    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)),sK2)),
% 2.26/0.66    inference(backward_demodulation,[],[f3592,f2381])).
% 2.26/0.66  fof(f2381,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f226,f237,f145])).
% 2.26/0.66  fof(f237,plain,(
% 2.26/0.66    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f103,f104,f148])).
% 2.26/0.66  fof(f148,plain,(
% 2.26/0.66    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.26/0.66    inference(cnf_transformation,[],[f76])).
% 2.26/0.66  fof(f76,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.26/0.66    inference(flattening,[],[f75])).
% 2.26/0.66  fof(f75,plain,(
% 2.26/0.66    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.26/0.66    inference(ennf_transformation,[],[f9])).
% 2.26/0.66  fof(f9,axiom,(
% 2.26/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 2.26/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).
% 2.26/0.66  fof(f3592,plain,(
% 2.26/0.66    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)),sK2)),
% 2.26/0.66    inference(backward_demodulation,[],[f3554,f2450])).
% 2.26/0.66  fof(f2450,plain,(
% 2.26/0.66    sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 2.26/0.66    inference(forward_demodulation,[],[f2390,f1590])).
% 2.26/0.66  fof(f1590,plain,(
% 2.26/0.66    sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))),
% 2.26/0.66    inference(backward_demodulation,[],[f1544,f1574])).
% 2.26/0.66  fof(f1574,plain,(
% 2.26/0.66    sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2)),
% 2.26/0.66    inference(backward_demodulation,[],[f389,f1567])).
% 2.26/0.66  fof(f1567,plain,(
% 2.26/0.66    sK2 = k3_lattices(sK0,sK2,k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f1566,f215])).
% 2.26/0.66  fof(f1566,plain,(
% 2.26/0.66    k7_lattices(sK0,k7_lattices(sK0,sK2)) = k3_lattices(sK0,sK2,k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f1565,f325])).
% 2.26/0.66  fof(f325,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),sK2) = k3_lattices(sK0,sK2,k5_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f172,f145])).
% 2.26/0.66  fof(f1565,plain,(
% 2.26/0.66    k7_lattices(sK0,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k5_lattices(sK0),sK2)),
% 2.26/0.66    inference(forward_demodulation,[],[f1564,f1522])).
% 2.26/0.66  fof(f1564,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),sK2) = k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(forward_demodulation,[],[f1563,f868])).
% 2.26/0.66  fof(f1563,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k6_lattices(sK0)),sK2)),
% 2.26/0.66    inference(forward_demodulation,[],[f1397,f215])).
% 2.26/0.66  fof(f1397,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k6_lattices(sK0)),k7_lattices(sK0,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f173,f226,f138])).
% 2.26/0.66  fof(f389,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k5_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,k5_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f388,f350])).
% 2.26/0.66  fof(f388,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,k5_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f290,f233])).
% 2.26/0.66  fof(f233,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f103,f104,f145])).
% 2.26/0.66  fof(f290,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,k5_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f104,f103,f172,f133])).
% 2.26/0.66  fof(f1544,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),sK2)),
% 2.26/0.66    inference(backward_demodulation,[],[f255,f1540])).
% 2.26/0.66  fof(f1540,plain,(
% 2.26/0.66    sK2 = k3_lattices(sK0,sK2,sK2)),
% 2.26/0.66    inference(forward_demodulation,[],[f1539,f215])).
% 2.26/0.66  fof(f1539,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,sK2) = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(forward_demodulation,[],[f1538,f1531])).
% 2.26/0.66  fof(f1531,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(backward_demodulation,[],[f1461,f1530])).
% 2.26/0.66  fof(f1530,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(forward_demodulation,[],[f1402,f1513])).
% 2.26/0.66  fof(f1513,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k1_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f1415,f883])).
% 2.26/0.66  fof(f883,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k3_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0))),
% 2.26/0.66    inference(backward_demodulation,[],[f562,f868])).
% 2.26/0.66  fof(f562,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k6_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f481,f533])).
% 2.26/0.66  fof(f481,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,sK2,k6_lattices(sK0))) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k6_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f104,f173,f138])).
% 2.26/0.66  fof(f1415,plain,(
% 2.26/0.66    k3_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0)) = k1_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f172,f226,f144])).
% 2.26/0.66  fof(f1402,plain,(
% 2.26/0.66    k7_lattices(sK0,sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,k7_lattices(sK0,sK2),k5_lattices(sK0)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f102,f171,f172,f226,f139])).
% 2.26/0.66  fof(f1461,plain,(
% 2.26/0.66    k2_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f168,f163,f226,f226,f149])).
% 2.26/0.66  fof(f1538,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,sK2) = k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(forward_demodulation,[],[f1399,f215])).
% 2.26/0.66  fof(f1399,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,k7_lattices(sK0,sK2)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f226,f226,f138])).
% 2.26/0.66  fof(f255,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK2))),
% 2.26/0.66    inference(forward_demodulation,[],[f211,f233])).
% 2.26/0.66  fof(f211,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK2))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f104,f103,f104,f133])).
% 2.26/0.66  fof(f2390,plain,(
% 2.26/0.66    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f104,f237,f145])).
% 2.26/0.66  fof(f3554,plain,(
% 2.26/0.66    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2))),
% 2.26/0.66    inference(backward_demodulation,[],[f3363,f2455])).
% 2.26/0.66  fof(f2455,plain,(
% 2.26/0.66    k4_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f2385,f1592])).
% 2.26/0.66  fof(f1592,plain,(
% 2.26/0.66    k4_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))),
% 2.26/0.66    inference(forward_demodulation,[],[f1580,f245])).
% 2.26/0.66  fof(f1580,plain,(
% 2.26/0.66    k4_lattices(sK0,sK2,sK1) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))),
% 2.26/0.66    inference(backward_demodulation,[],[f1012,f1567])).
% 2.26/0.66  fof(f1012,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k5_lattices(sK0)),sK1)),
% 2.26/0.66    inference(backward_demodulation,[],[f414,f1003])).
% 2.26/0.66  fof(f1003,plain,(
% 2.26/0.66    sK1 = k3_lattices(sK0,sK1,k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f1002,f181])).
% 2.26/0.66  fof(f1002,plain,(
% 2.26/0.66    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k3_lattices(sK0,sK1,k5_lattices(sK0))),
% 2.26/0.66    inference(forward_demodulation,[],[f1001,f324])).
% 2.26/0.66  fof(f324,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k5_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f103,f172,f145])).
% 2.26/0.66  fof(f1001,plain,(
% 2.26/0.66    k7_lattices(sK0,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 2.26/0.66    inference(forward_demodulation,[],[f1000,f857])).
% 2.26/0.66  fof(f1000,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),sK1) = k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)))),
% 2.26/0.66    inference(forward_demodulation,[],[f999,f868])).
% 2.26/0.66  fof(f999,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k6_lattices(sK0)),sK1)),
% 2.26/0.66    inference(forward_demodulation,[],[f758,f181])).
% 2.26/0.66  fof(f758,plain,(
% 2.26/0.66    k7_lattices(sK0,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k6_lattices(sK0)),k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f101,f102,f173,f188,f138])).
% 2.26/0.66  fof(f414,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k5_lattices(sK0)),k3_lattices(sK0,sK1,k5_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f413,f245])).
% 2.26/0.66  fof(f413,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k5_lattices(sK0)),k3_lattices(sK0,sK1,k5_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f412,f325])).
% 2.26/0.66  fof(f412,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k5_lattices(sK0),sK2),k3_lattices(sK0,sK1,k5_lattices(sK0)))),
% 2.26/0.66    inference(forward_demodulation,[],[f274,f324])).
% 2.26/0.66  fof(f274,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,k5_lattices(sK0),sK2),k3_lattices(sK0,k5_lattices(sK0),sK1))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f103,f104,f172,f133])).
% 2.26/0.66  fof(f2385,plain,(
% 2.26/0.66    k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f167,f164,f172,f237,f145])).
% 2.26/0.66  fof(f3363,plain,(
% 2.26/0.66    k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k5_lattices(sK0)) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2))),
% 2.26/0.66    inference(forward_demodulation,[],[f2217,f217])).
% 2.26/0.66  fof(f2217,plain,(
% 2.26/0.66    k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2))),
% 2.26/0.66    inference(unit_resulting_resolution,[],[f99,f100,f165,f102,f104,f226,f237,f133])).
% 2.26/0.66  fof(f156,plain,(
% 2.26/0.66    k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) | spl6_1),
% 2.26/0.66    inference(avatar_component_clause,[],[f154])).
% 2.26/0.66  fof(f162,plain,(
% 2.26/0.66    spl6_1 | spl6_2),
% 2.26/0.66    inference(avatar_split_clause,[],[f105,f158,f154])).
% 2.26/0.66  fof(f105,plain,(
% 2.26/0.66    r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)),
% 2.26/0.66    inference(cnf_transformation,[],[f86])).
% 2.26/0.66  fof(f161,plain,(
% 2.26/0.66    ~spl6_1 | ~spl6_2),
% 2.26/0.66    inference(avatar_split_clause,[],[f106,f158,f154])).
% 2.26/0.66  fof(f106,plain,(
% 2.26/0.66    ~r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2)),
% 2.26/0.66    inference(cnf_transformation,[],[f86])).
% 2.26/0.66  % SZS output end Proof for theBenchmark
% 2.26/0.66  % (17856)------------------------------
% 2.26/0.66  % (17856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.66  % (17856)Termination reason: Refutation
% 2.26/0.66  
% 2.26/0.66  % (17856)Memory used [KB]: 13048
% 2.26/0.66  % (17856)Time elapsed: 0.251 s
% 2.26/0.66  % (17856)------------------------------
% 2.26/0.66  % (17856)------------------------------
% 2.26/0.67  % (17843)Success in time 0.302 s
%------------------------------------------------------------------------------
