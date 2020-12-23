%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1560+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:24 EST 2020

% Result     : Theorem 53.00s
% Output     : Refutation 53.00s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 698 expanded)
%              Number of leaves         :   20 ( 223 expanded)
%              Depth                    :   21
%              Number of atoms          :  529 (4416 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37225,plain,(
    $false ),
    inference(subsumption_resolution,[],[f37203,f15319])).

fof(f15319,plain,(
    v1_xboole_0(u1_struct_0(sK34)) ),
    inference(subsumption_resolution,[],[f15297,f14449])).

fof(f14449,plain,(
    r2_yellow_0(sK34,k1_tarski(sK35)) ),
    inference(resolution,[],[f14135,f5181])).

fof(f5181,plain,(
    ! [X1] :
      ( ~ sP0(sK34,X1)
      | r2_yellow_0(sK34,X1) ) ),
    inference(resolution,[],[f4833,f3888])).

fof(f3888,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP0(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f3511])).

fof(f3511,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f3454])).

fof(f3454,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f4833,plain,(
    sP1(sK34) ),
    inference(subsumption_resolution,[],[f4817,f3884])).

fof(f3884,plain,(
    l1_orders_2(sK34) ),
    inference(cnf_transformation,[],[f3510])).

fof(f3510,plain,
    ( ( ~ r2_yellow_0(sK34,k6_domain_1(u1_struct_0(sK34),sK35))
      | ~ r1_yellow_0(sK34,k6_domain_1(u1_struct_0(sK34),sK35)) )
    & m1_subset_1(sK35,u1_struct_0(sK34))
    & l1_orders_2(sK34)
    & v5_orders_2(sK34)
    & v3_orders_2(sK34)
    & ~ v2_struct_0(sK34) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK34,sK35])],[f3048,f3509,f3508])).

fof(f3508,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ r2_yellow_0(sK34,k6_domain_1(u1_struct_0(sK34),X1))
            | ~ r1_yellow_0(sK34,k6_domain_1(u1_struct_0(sK34),X1)) )
          & m1_subset_1(X1,u1_struct_0(sK34)) )
      & l1_orders_2(sK34)
      & v5_orders_2(sK34)
      & v3_orders_2(sK34)
      & ~ v2_struct_0(sK34) ) ),
    introduced(choice_axiom,[])).

fof(f3509,plain,
    ( ? [X1] :
        ( ( ~ r2_yellow_0(sK34,k6_domain_1(u1_struct_0(sK34),X1))
          | ~ r1_yellow_0(sK34,k6_domain_1(u1_struct_0(sK34),X1)) )
        & m1_subset_1(X1,u1_struct_0(sK34)) )
   => ( ( ~ r2_yellow_0(sK34,k6_domain_1(u1_struct_0(sK34),sK35))
        | ~ r1_yellow_0(sK34,k6_domain_1(u1_struct_0(sK34),sK35)) )
      & m1_subset_1(sK35,u1_struct_0(sK34)) ) ),
    introduced(choice_axiom,[])).

fof(f3048,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            | ~ r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3047])).

fof(f3047,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            | ~ r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3015])).

fof(f3015,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
              & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3014])).

fof(f3014,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_0)).

fof(f4817,plain,
    ( sP1(sK34)
    | ~ l1_orders_2(sK34) ),
    inference(resolution,[],[f3883,f3895])).

fof(f3895,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3455,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f3050,f3454,f3453])).

fof(f3453,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ? [X2] :
          ( ! [X3] :
              ( r1_orders_2(X0,X3,X2)
              | ~ r1_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3050,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3049])).

fof(f3049,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2990])).

fof(f2990,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(f3883,plain,(
    v5_orders_2(sK34) ),
    inference(cnf_transformation,[],[f3510])).

fof(f14135,plain,(
    sP0(sK34,k1_tarski(sK35)) ),
    inference(subsumption_resolution,[],[f14134,f5656])).

fof(f5656,plain,
    ( sP0(sK34,k1_tarski(sK35))
    | m1_subset_1(sK36(sK34,k1_tarski(sK35),sK35),u1_struct_0(sK34)) ),
    inference(subsumption_resolution,[],[f5619,f3885])).

fof(f3885,plain,(
    m1_subset_1(sK35,u1_struct_0(sK34)) ),
    inference(cnf_transformation,[],[f3510])).

fof(f5619,plain,
    ( sP0(sK34,k1_tarski(sK35))
    | m1_subset_1(sK36(sK34,k1_tarski(sK35),sK35),u1_struct_0(sK34))
    | ~ m1_subset_1(sK35,u1_struct_0(sK34)) ),
    inference(resolution,[],[f5284,f3892])).

fof(f3892,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK36(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3516])).

fof(f3516,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ( ~ r1_orders_2(X0,sK36(X0,X1,X2),X2)
              & r1_lattice3(X0,X1,sK36(X0,X1,X2))
              & m1_subset_1(sK36(X0,X1,X2),u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ( ! [X5] :
              ( r1_orders_2(X0,X5,sK37(X0,X1))
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,sK37(X0,X1))
          & m1_subset_1(sK37(X0,X1),u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK36,sK37])],[f3513,f3515,f3514])).

fof(f3514,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK36(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK36(X0,X1,X2))
        & m1_subset_1(sK36(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3515,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK37(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK37(X0,X1))
        & m1_subset_1(sK37(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3513,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(X0,X3,X2)
                & r1_lattice3(X0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X4] :
            ( ! [X5] :
                ( r1_orders_2(X0,X5,X4)
                | ~ r1_lattice3(X0,X1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X4)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f3512])).

fof(f3512,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(X0,X3,X2)
                & r1_lattice3(X0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r1_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3453])).

fof(f5284,plain,(
    r1_lattice3(sK34,k1_tarski(sK35),sK35) ),
    inference(subsumption_resolution,[],[f5283,f3884])).

fof(f5283,plain,
    ( r1_lattice3(sK34,k1_tarski(sK35),sK35)
    | ~ l1_orders_2(sK34) ),
    inference(subsumption_resolution,[],[f5268,f3885])).

fof(f5268,plain,
    ( r1_lattice3(sK34,k1_tarski(sK35),sK35)
    | ~ m1_subset_1(sK35,u1_struct_0(sK34))
    | ~ l1_orders_2(sK34) ),
    inference(duplicate_literal_removal,[],[f5231])).

fof(f5231,plain,
    ( r1_lattice3(sK34,k1_tarski(sK35),sK35)
    | ~ m1_subset_1(sK35,u1_struct_0(sK34))
    | ~ m1_subset_1(sK35,u1_struct_0(sK34))
    | ~ l1_orders_2(sK34) ),
    inference(resolution,[],[f5089,f3980])).

fof(f3980,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3084])).

fof(f3084,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3020])).

fof(f3020,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f5089,plain,(
    r1_orders_2(sK34,sK35,sK35) ),
    inference(subsumption_resolution,[],[f5088,f3881])).

fof(f3881,plain,(
    ~ v2_struct_0(sK34) ),
    inference(cnf_transformation,[],[f3510])).

fof(f5088,plain,
    ( r1_orders_2(sK34,sK35,sK35)
    | v2_struct_0(sK34) ),
    inference(subsumption_resolution,[],[f5087,f3882])).

fof(f3882,plain,(
    v3_orders_2(sK34) ),
    inference(cnf_transformation,[],[f3510])).

fof(f5087,plain,
    ( r1_orders_2(sK34,sK35,sK35)
    | ~ v3_orders_2(sK34)
    | v2_struct_0(sK34) ),
    inference(subsumption_resolution,[],[f4969,f3884])).

fof(f4969,plain,
    ( r1_orders_2(sK34,sK35,sK35)
    | ~ l1_orders_2(sK34)
    | ~ v3_orders_2(sK34)
    | v2_struct_0(sK34) ),
    inference(resolution,[],[f3885,f3958])).

fof(f3958,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3074])).

fof(f3074,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3073])).

fof(f3073,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1952])).

fof(f1952,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f14134,plain,
    ( sP0(sK34,k1_tarski(sK35))
    | ~ m1_subset_1(sK36(sK34,k1_tarski(sK35),sK35),u1_struct_0(sK34)) ),
    inference(subsumption_resolution,[],[f14133,f5658])).

fof(f5658,plain,
    ( sP0(sK34,k1_tarski(sK35))
    | ~ r1_orders_2(sK34,sK36(sK34,k1_tarski(sK35),sK35),sK35) ),
    inference(subsumption_resolution,[],[f5621,f3885])).

fof(f5621,plain,
    ( sP0(sK34,k1_tarski(sK35))
    | ~ r1_orders_2(sK34,sK36(sK34,k1_tarski(sK35),sK35),sK35)
    | ~ m1_subset_1(sK35,u1_struct_0(sK34)) ),
    inference(resolution,[],[f5284,f3894])).

fof(f3894,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_orders_2(X0,sK36(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3516])).

fof(f14133,plain,
    ( sP0(sK34,k1_tarski(sK35))
    | r1_orders_2(sK34,sK36(sK34,k1_tarski(sK35),sK35),sK35)
    | ~ m1_subset_1(sK36(sK34,k1_tarski(sK35),sK35),u1_struct_0(sK34)) ),
    inference(subsumption_resolution,[],[f14107,f5284])).

fof(f14107,plain,
    ( sP0(sK34,k1_tarski(sK35))
    | ~ r1_lattice3(sK34,k1_tarski(sK35),sK35)
    | r1_orders_2(sK34,sK36(sK34,k1_tarski(sK35),sK35),sK35)
    | ~ m1_subset_1(sK36(sK34,k1_tarski(sK35),sK35),u1_struct_0(sK34)) ),
    inference(resolution,[],[f4939,f5120])).

fof(f5120,plain,(
    ! [X82] :
      ( ~ r1_lattice3(sK34,k1_tarski(sK35),X82)
      | r1_orders_2(sK34,X82,sK35)
      | ~ m1_subset_1(X82,u1_struct_0(sK34)) ) ),
    inference(subsumption_resolution,[],[f4996,f3884])).

fof(f4996,plain,(
    ! [X82] :
      ( r1_orders_2(sK34,X82,sK35)
      | ~ r1_lattice3(sK34,k1_tarski(sK35),X82)
      | ~ m1_subset_1(X82,u1_struct_0(sK34))
      | ~ l1_orders_2(sK34) ) ),
    inference(resolution,[],[f3885,f3979])).

fof(f3979,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3084])).

fof(f4939,plain,(
    ! [X2] :
      ( r1_lattice3(sK34,X2,sK36(sK34,X2,sK35))
      | sP0(sK34,X2)
      | ~ r1_lattice3(sK34,X2,sK35) ) ),
    inference(resolution,[],[f3885,f3893])).

fof(f3893,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | r1_lattice3(X0,X1,sK36(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3516])).

fof(f15297,plain,
    ( ~ r2_yellow_0(sK34,k1_tarski(sK35))
    | v1_xboole_0(u1_struct_0(sK34)) ),
    inference(resolution,[],[f14636,f5194])).

fof(f5194,plain,
    ( ~ r1_yellow_0(sK34,k1_tarski(sK35))
    | ~ r2_yellow_0(sK34,k1_tarski(sK35))
    | v1_xboole_0(u1_struct_0(sK34)) ),
    inference(subsumption_resolution,[],[f5186,f3885])).

fof(f5186,plain,
    ( ~ r1_yellow_0(sK34,k1_tarski(sK35))
    | ~ r2_yellow_0(sK34,k1_tarski(sK35))
    | ~ m1_subset_1(sK35,u1_struct_0(sK34))
    | v1_xboole_0(u1_struct_0(sK34)) ),
    inference(superposition,[],[f3886,f3952])).

fof(f3952,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3068])).

fof(f3068,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3067])).

fof(f3067,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1935])).

fof(f1935,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f3886,plain,
    ( ~ r1_yellow_0(sK34,k6_domain_1(u1_struct_0(sK34),sK35))
    | ~ r2_yellow_0(sK34,k6_domain_1(u1_struct_0(sK34),sK35)) ),
    inference(cnf_transformation,[],[f3510])).

fof(f14636,plain,(
    r1_yellow_0(sK34,k1_tarski(sK35)) ),
    inference(resolution,[],[f14508,f5196])).

fof(f5196,plain,(
    ! [X1] :
      ( ~ sP5(sK34,X1)
      | r1_yellow_0(sK34,X1) ) ),
    inference(resolution,[],[f4838,f3922])).

fof(f3922,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP5(X0,X1)
      | ~ sP6(X0) ) ),
    inference(cnf_transformation,[],[f3533])).

fof(f3533,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ~ sP5(X0,X1) )
          & ( sP5(X0,X1)
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ sP6(X0) ) ),
    inference(nnf_transformation,[],[f3461])).

fof(f3461,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> sP5(X0,X1) )
      | ~ sP6(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f4838,plain,(
    sP6(sK34) ),
    inference(subsumption_resolution,[],[f4824,f3884])).

fof(f4824,plain,
    ( sP6(sK34)
    | ~ l1_orders_2(sK34) ),
    inference(resolution,[],[f3883,f3929])).

fof(f3929,plain,(
    ! [X0] :
      ( sP6(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3462,plain,(
    ! [X0] :
      ( sP6(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f3060,f3461,f3460])).

fof(f3460,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
    <=> ? [X2] :
          ( ! [X3] :
              ( r1_orders_2(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f3060,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3059])).

fof(f3059,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2989])).

fof(f2989,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f14508,plain,(
    sP5(sK34,k1_tarski(sK35)) ),
    inference(subsumption_resolution,[],[f14507,f6020])).

fof(f6020,plain,
    ( sP5(sK34,k1_tarski(sK35))
    | m1_subset_1(sK44(sK34,k1_tarski(sK35),sK35),u1_struct_0(sK34)) ),
    inference(subsumption_resolution,[],[f5982,f3885])).

fof(f5982,plain,
    ( sP5(sK34,k1_tarski(sK35))
    | m1_subset_1(sK44(sK34,k1_tarski(sK35),sK35),u1_struct_0(sK34))
    | ~ m1_subset_1(sK35,u1_struct_0(sK34)) ),
    inference(resolution,[],[f5286,f3926])).

fof(f3926,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1)
      | m1_subset_1(sK44(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3538])).

fof(f3538,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ! [X2] :
            ( ( ~ r1_orders_2(X0,X2,sK44(X0,X1,X2))
              & r2_lattice3(X0,X1,sK44(X0,X1,X2))
              & m1_subset_1(sK44(X0,X1,X2),u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ( ! [X5] :
              ( r1_orders_2(X0,sK45(X0,X1),X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,sK45(X0,X1))
          & m1_subset_1(sK45(X0,X1),u1_struct_0(X0)) )
        | ~ sP5(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK44,sK45])],[f3535,f3537,f3536])).

fof(f3536,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK44(X0,X1,X2))
        & r2_lattice3(X0,X1,sK44(X0,X1,X2))
        & m1_subset_1(sK44(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3537,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK45(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK45(X0,X1))
        & m1_subset_1(sK45(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3535,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ! [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(X0,X2,X3)
                & r2_lattice3(X0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X4] :
            ( ! [X5] :
                ( r1_orders_2(X0,X4,X5)
                | ~ r2_lattice3(X0,X1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X4)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP5(X0,X1) ) ) ),
    inference(rectify,[],[f3534])).

fof(f3534,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ! [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(X0,X2,X3)
                & r2_lattice3(X0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP5(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3460])).

fof(f5286,plain,(
    r2_lattice3(sK34,k1_tarski(sK35),sK35) ),
    inference(subsumption_resolution,[],[f5285,f3884])).

fof(f5285,plain,
    ( r2_lattice3(sK34,k1_tarski(sK35),sK35)
    | ~ l1_orders_2(sK34) ),
    inference(subsumption_resolution,[],[f5267,f3885])).

fof(f5267,plain,
    ( r2_lattice3(sK34,k1_tarski(sK35),sK35)
    | ~ m1_subset_1(sK35,u1_struct_0(sK34))
    | ~ l1_orders_2(sK34) ),
    inference(duplicate_literal_removal,[],[f5232])).

fof(f5232,plain,
    ( r2_lattice3(sK34,k1_tarski(sK35),sK35)
    | ~ m1_subset_1(sK35,u1_struct_0(sK34))
    | ~ m1_subset_1(sK35,u1_struct_0(sK34))
    | ~ l1_orders_2(sK34) ),
    inference(resolution,[],[f5089,f3982])).

fof(f3982,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3084])).

fof(f14507,plain,
    ( sP5(sK34,k1_tarski(sK35))
    | ~ m1_subset_1(sK44(sK34,k1_tarski(sK35),sK35),u1_struct_0(sK34)) ),
    inference(subsumption_resolution,[],[f14506,f6022])).

fof(f6022,plain,
    ( sP5(sK34,k1_tarski(sK35))
    | ~ r1_orders_2(sK34,sK35,sK44(sK34,k1_tarski(sK35),sK35)) ),
    inference(subsumption_resolution,[],[f5984,f3885])).

fof(f5984,plain,
    ( sP5(sK34,k1_tarski(sK35))
    | ~ r1_orders_2(sK34,sK35,sK44(sK34,k1_tarski(sK35),sK35))
    | ~ m1_subset_1(sK35,u1_struct_0(sK34)) ),
    inference(resolution,[],[f5286,f3928])).

fof(f3928,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1)
      | ~ r1_orders_2(X0,X2,sK44(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3538])).

fof(f14506,plain,
    ( sP5(sK34,k1_tarski(sK35))
    | r1_orders_2(sK34,sK35,sK44(sK34,k1_tarski(sK35),sK35))
    | ~ m1_subset_1(sK44(sK34,k1_tarski(sK35),sK35),u1_struct_0(sK34)) ),
    inference(subsumption_resolution,[],[f14476,f5286])).

fof(f14476,plain,
    ( sP5(sK34,k1_tarski(sK35))
    | ~ r2_lattice3(sK34,k1_tarski(sK35),sK35)
    | r1_orders_2(sK34,sK35,sK44(sK34,k1_tarski(sK35),sK35))
    | ~ m1_subset_1(sK44(sK34,k1_tarski(sK35),sK35),u1_struct_0(sK34)) ),
    inference(resolution,[],[f4953,f5124])).

fof(f5124,plain,(
    ! [X86] :
      ( ~ r2_lattice3(sK34,k1_tarski(sK35),X86)
      | r1_orders_2(sK34,sK35,X86)
      | ~ m1_subset_1(X86,u1_struct_0(sK34)) ) ),
    inference(subsumption_resolution,[],[f5000,f3884])).

fof(f5000,plain,(
    ! [X86] :
      ( r1_orders_2(sK34,sK35,X86)
      | ~ r2_lattice3(sK34,k1_tarski(sK35),X86)
      | ~ m1_subset_1(X86,u1_struct_0(sK34))
      | ~ l1_orders_2(sK34) ) ),
    inference(resolution,[],[f3885,f3981])).

fof(f3981,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3084])).

fof(f4953,plain,(
    ! [X20] :
      ( r2_lattice3(sK34,X20,sK44(sK34,X20,sK35))
      | sP5(sK34,X20)
      | ~ r2_lattice3(sK34,X20,sK35) ) ),
    inference(resolution,[],[f3885,f3927])).

fof(f3927,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1)
      | r2_lattice3(X0,X1,sK44(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f3538])).

fof(f37203,plain,(
    ~ v1_xboole_0(u1_struct_0(sK34)) ),
    inference(resolution,[],[f8426,f35510])).

fof(f35510,plain,(
    ~ v1_xboole_0(u1_orders_2(sK34)) ),
    inference(resolution,[],[f5300,f4099])).

fof(f4099,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3137])).

fof(f3137,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f5300,plain,(
    r2_hidden(k4_tarski(sK35,sK35),u1_orders_2(sK34)) ),
    inference(subsumption_resolution,[],[f5299,f3884])).

fof(f5299,plain,
    ( r2_hidden(k4_tarski(sK35,sK35),u1_orders_2(sK34))
    | ~ l1_orders_2(sK34) ),
    inference(subsumption_resolution,[],[f5266,f3885])).

fof(f5266,plain,
    ( r2_hidden(k4_tarski(sK35,sK35),u1_orders_2(sK34))
    | ~ m1_subset_1(sK35,u1_struct_0(sK34))
    | ~ l1_orders_2(sK34) ),
    inference(duplicate_literal_removal,[],[f5243])).

fof(f5243,plain,
    ( r2_hidden(k4_tarski(sK35,sK35),u1_orders_2(sK34))
    | ~ m1_subset_1(sK35,u1_struct_0(sK34))
    | ~ m1_subset_1(sK35,u1_struct_0(sK34))
    | ~ l1_orders_2(sK34) ),
    inference(resolution,[],[f5089,f4074])).

fof(f4074,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3596])).

fof(f3596,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3128])).

fof(f3128,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1885])).

fof(f1885,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f8426,plain,
    ( v1_xboole_0(u1_orders_2(sK34))
    | ~ v1_xboole_0(u1_struct_0(sK34)) ),
    inference(resolution,[],[f4904,f4103])).

fof(f4103,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3143])).

fof(f3143,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1212])).

fof(f1212,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f4904,plain,(
    m1_subset_1(u1_orders_2(sK34),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK34),u1_struct_0(sK34)))) ),
    inference(resolution,[],[f3884,f4076])).

fof(f4076,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3129])).

fof(f3129,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
%------------------------------------------------------------------------------
