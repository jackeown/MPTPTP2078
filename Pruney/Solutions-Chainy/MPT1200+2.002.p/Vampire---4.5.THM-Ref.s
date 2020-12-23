%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:37 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 347 expanded)
%              Number of leaves         :   16 ( 145 expanded)
%              Depth                    :   29
%              Number of atoms          :  498 (2906 expanded)
%              Number of equality atoms :   62 (  62 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1505,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1504,f44])).

fof(f44,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))
    & r1_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & v7_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                    & r1_lattices(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3))
                  & r1_lattices(sK0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & v7_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3))
                & r1_lattices(sK0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,X2,X3))
              & r1_lattices(sK0,sK1,X2)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,X2,X3))
            & r1_lattices(sK0,sK1,X2)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,sK2,X3))
          & r1_lattices(sK0,sK1,sK2)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,sK2,X3))
        & r1_lattices(sK0,sK1,sK2)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))
      & r1_lattices(sK0,sK1,sK2)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).

fof(f1504,plain,(
    ~ l3_lattices(sK0) ),
    inference(resolution,[],[f1503,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f1503,plain,(
    ~ l1_lattices(sK0) ),
    inference(subsumption_resolution,[],[f1502,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1502,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1501,f46])).

fof(f46,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f1501,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1500,f47])).

fof(f47,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f1500,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1499,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f1499,plain,(
    ~ m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1498,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f1498,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1492,f49])).

fof(f49,plain,(
    ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f1492,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    inference(superposition,[],[f89,f1475])).

fof(f1475,plain,(
    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)) ),
    inference(subsumption_resolution,[],[f1460,f46])).

fof(f1460,plain,
    ( k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[],[f1450,f100])).

fof(f100,plain,(
    sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f99,f45])).

fof(f99,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f96,f46])).

fof(f96,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f95,f48])).

fof(f48,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f93,f42])).

fof(f42,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f92,f44])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k2_lattices(sK0,X0,X1) = X0
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f54,f43])).

fof(f43,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f1450,plain,(
    ! [X5] :
      ( k2_lattices(sK0,sK1,k2_lattices(sK0,X5,sK3)) = k2_lattices(sK0,k2_lattices(sK0,sK1,X5),sK3)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f141,f45])).

fof(f141,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_lattices(sK0,X4,k2_lattices(sK0,X5,sK3)) = k2_lattices(sK0,k2_lattices(sK0,X4,X5),sK3)
      | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f138,f47])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,k2_lattices(sK0,X0,X2)) = k2_lattices(sK0,k2_lattices(sK0,X1,X0),X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f137,f44])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,k2_lattices(sK0,X0,X2)) = k2_lattices(sK0,k2_lattices(sK0,X1,X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f136,f50])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k2_lattices(sK0,X2,k2_lattices(sK0,X1,X0)) = k2_lattices(sK0,k2_lattices(sK0,X2,X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f135,f40])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k2_lattices(sK0,X2,k2_lattices(sK0,X1,X0)) = k2_lattices(sK0,k2_lattices(sK0,X2,X1),X0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f56,f41])).

fof(f41,plain,(
    v7_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v7_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattices)).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f88,f44])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f87,f50])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_lattices(sK0)
      | r1_lattices(sK0,k2_lattices(sK0,X1,X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X1,X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X1,X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f84,f65])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_lattices(sK0,X1,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X1,X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f83,f44])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_lattices(sK0,X1,X0),u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X1,X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f82,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l2_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( X1 != X1
      | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X1 != X1
      | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f53,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f75,f40])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f74,f44])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f61,f42])).

fof(f61,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f36,f38,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0))
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (23186)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.48  % (23171)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (23178)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (23177)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (23187)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (23177)Refutation not found, incomplete strategy% (23177)------------------------------
% 0.21/0.50  % (23177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23177)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23177)Memory used [KB]: 10618
% 0.21/0.50  % (23177)Time elapsed: 0.065 s
% 0.21/0.50  % (23177)------------------------------
% 0.21/0.50  % (23177)------------------------------
% 0.21/0.50  % (23185)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (23169)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (23185)Refutation not found, incomplete strategy% (23185)------------------------------
% 0.21/0.51  % (23185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23185)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23185)Memory used [KB]: 1663
% 0.21/0.51  % (23185)Time elapsed: 0.077 s
% 0.21/0.51  % (23185)------------------------------
% 0.21/0.51  % (23185)------------------------------
% 0.21/0.51  % (23174)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.52  % (23184)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (23179)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (23179)Refutation not found, incomplete strategy% (23179)------------------------------
% 0.21/0.52  % (23179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23179)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23179)Memory used [KB]: 10618
% 0.21/0.52  % (23179)Time elapsed: 0.101 s
% 0.21/0.52  % (23179)------------------------------
% 0.21/0.52  % (23179)------------------------------
% 0.21/0.52  % (23189)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (23176)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (23175)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (23170)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (23176)Refutation not found, incomplete strategy% (23176)------------------------------
% 0.21/0.52  % (23176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23176)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23176)Memory used [KB]: 6140
% 0.21/0.52  % (23176)Time elapsed: 0.117 s
% 0.21/0.52  % (23176)------------------------------
% 0.21/0.52  % (23176)------------------------------
% 0.21/0.52  % (23190)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (23181)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (23180)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.53  % (23172)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.53  % (23172)Refutation not found, incomplete strategy% (23172)------------------------------
% 0.21/0.53  % (23172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23172)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23172)Memory used [KB]: 10618
% 0.21/0.53  % (23172)Time elapsed: 0.115 s
% 0.21/0.53  % (23172)------------------------------
% 0.21/0.53  % (23172)------------------------------
% 0.21/0.53  % (23173)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.53  % (23191)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.53  % (23188)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.54  % (23183)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.54  % (23182)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.54  % (23192)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.54  % (23192)Refutation not found, incomplete strategy% (23192)------------------------------
% 0.21/0.54  % (23192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23192)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23192)Memory used [KB]: 10618
% 0.21/0.54  % (23192)Time elapsed: 0.103 s
% 0.21/0.54  % (23192)------------------------------
% 0.21/0.54  % (23192)------------------------------
% 1.89/0.62  % (23188)Refutation found. Thanks to Tanya!
% 1.89/0.62  % SZS status Theorem for theBenchmark
% 1.89/0.62  % SZS output start Proof for theBenchmark
% 1.89/0.62  fof(f1505,plain,(
% 1.89/0.62    $false),
% 1.89/0.62    inference(subsumption_resolution,[],[f1504,f44])).
% 1.89/0.62  fof(f44,plain,(
% 1.89/0.62    l3_lattices(sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f26,plain,(
% 1.89/0.62    (((~r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & v7_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f25,f24,f23,f22])).
% 1.89/0.62  fof(f22,plain,(
% 1.89/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & v7_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f23,plain,(
% 1.89/0.62    ? [X1] : (? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f24,plain,(
% 1.89/0.62    ? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,sK2,X3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f25,plain,(
% 1.89/0.62    ? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,sK2,X3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f10,plain,(
% 1.89/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0))),
% 1.89/0.62    inference(flattening,[],[f9])).
% 1.89/0.62  fof(f9,plain,(
% 1.89/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f8])).
% 1.89/0.62  fof(f8,negated_conjecture,(
% 1.89/0.62    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 1.89/0.62    inference(negated_conjecture,[],[f7])).
% 1.89/0.62  fof(f7,conjecture,(
% 1.89/0.62    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).
% 1.89/0.62  fof(f1504,plain,(
% 1.89/0.62    ~l3_lattices(sK0)),
% 1.89/0.62    inference(resolution,[],[f1503,f50])).
% 1.89/0.62  fof(f50,plain,(
% 1.89/0.62    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f11])).
% 1.89/0.62  fof(f11,plain,(
% 1.89/0.62    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f5])).
% 1.89/0.62  fof(f5,axiom,(
% 1.89/0.62    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.89/0.62  fof(f1503,plain,(
% 1.89/0.62    ~l1_lattices(sK0)),
% 1.89/0.62    inference(subsumption_resolution,[],[f1502,f40])).
% 1.89/0.62  fof(f40,plain,(
% 1.89/0.62    ~v2_struct_0(sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f1502,plain,(
% 1.89/0.62    ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 1.89/0.62    inference(subsumption_resolution,[],[f1501,f46])).
% 1.89/0.62  fof(f46,plain,(
% 1.89/0.62    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f1501,plain,(
% 1.89/0.62    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 1.89/0.62    inference(subsumption_resolution,[],[f1500,f47])).
% 1.89/0.62  fof(f47,plain,(
% 1.89/0.62    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f1500,plain,(
% 1.89/0.62    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)),
% 1.89/0.62    inference(resolution,[],[f1499,f65])).
% 1.89/0.62  fof(f65,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f21])).
% 1.89/0.62  fof(f21,plain,(
% 1.89/0.62    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(flattening,[],[f20])).
% 1.89/0.62  fof(f20,plain,(
% 1.89/0.62    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f4])).
% 1.89/0.62  fof(f4,axiom,(
% 1.89/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).
% 1.89/0.62  fof(f1499,plain,(
% 1.89/0.62    ~m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))),
% 1.89/0.62    inference(subsumption_resolution,[],[f1498,f45])).
% 1.89/0.62  fof(f45,plain,(
% 1.89/0.62    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f1498,plain,(
% 1.89/0.62    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))),
% 1.89/0.62    inference(subsumption_resolution,[],[f1492,f49])).
% 1.89/0.62  fof(f49,plain,(
% 1.89/0.62    ~r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f1492,plain,(
% 1.89/0.62    r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))),
% 1.89/0.62    inference(superposition,[],[f89,f1475])).
% 1.89/0.62  fof(f1475,plain,(
% 1.89/0.62    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3))),
% 1.89/0.62    inference(subsumption_resolution,[],[f1460,f46])).
% 1.89/0.62  fof(f1460,plain,(
% 1.89/0.62    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.89/0.62    inference(superposition,[],[f1450,f100])).
% 1.89/0.62  fof(f100,plain,(
% 1.89/0.62    sK1 = k2_lattices(sK0,sK1,sK2)),
% 1.89/0.62    inference(subsumption_resolution,[],[f99,f45])).
% 1.89/0.62  fof(f99,plain,(
% 1.89/0.62    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,sK2)),
% 1.89/0.62    inference(subsumption_resolution,[],[f96,f46])).
% 1.89/0.62  fof(f96,plain,(
% 1.89/0.62    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,sK2)),
% 1.89/0.62    inference(resolution,[],[f95,f48])).
% 1.89/0.62  fof(f48,plain,(
% 1.89/0.62    r1_lattices(sK0,sK1,sK2)),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f95,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f94,f40])).
% 1.89/0.62  fof(f94,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | v2_struct_0(sK0)) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f93,f42])).
% 1.89/0.62  fof(f42,plain,(
% 1.89/0.62    v8_lattices(sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f93,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f92,f44])).
% 1.89/0.62  fof(f92,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k2_lattices(sK0,X0,X1) = X0 | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.89/0.62    inference(resolution,[],[f54,f43])).
% 1.89/0.62  fof(f43,plain,(
% 1.89/0.62    v9_lattices(sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f54,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f28])).
% 1.89/0.62  fof(f28,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(nnf_transformation,[],[f15])).
% 1.89/0.62  fof(f15,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(flattening,[],[f14])).
% 1.89/0.62  fof(f14,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f6])).
% 1.89/0.62  fof(f6,axiom,(
% 1.89/0.62    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 1.89/0.62  fof(f1450,plain,(
% 1.89/0.62    ( ! [X5] : (k2_lattices(sK0,sK1,k2_lattices(sK0,X5,sK3)) = k2_lattices(sK0,k2_lattices(sK0,sK1,X5),sK3) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(resolution,[],[f141,f45])).
% 1.89/0.62  fof(f141,plain,(
% 1.89/0.62    ( ! [X4,X5] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,X4,k2_lattices(sK0,X5,sK3)) = k2_lattices(sK0,k2_lattices(sK0,X4,X5),sK3) | ~m1_subset_1(X5,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(resolution,[],[f138,f47])).
% 1.89/0.62  fof(f138,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,k2_lattices(sK0,X0,X2)) = k2_lattices(sK0,k2_lattices(sK0,X1,X0),X2) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f137,f44])).
% 1.89/0.62  fof(f137,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,k2_lattices(sK0,X0,X2)) = k2_lattices(sK0,k2_lattices(sK0,X1,X0),X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 1.89/0.62    inference(resolution,[],[f136,f50])).
% 1.89/0.62  fof(f136,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~l1_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X2,k2_lattices(sK0,X1,X0)) = k2_lattices(sK0,k2_lattices(sK0,X2,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f135,f40])).
% 1.89/0.62  fof(f135,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X2,k2_lattices(sK0,X1,X0)) = k2_lattices(sK0,k2_lattices(sK0,X2,X1),X0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.89/0.62    inference(resolution,[],[f56,f41])).
% 1.89/0.62  fof(f41,plain,(
% 1.89/0.62    v7_lattices(sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f26])).
% 1.89/0.62  fof(f56,plain,(
% 1.89/0.62    ( ! [X6,X4,X0,X5] : (~v7_lattices(X0) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f34])).
% 1.89/0.62  fof(f34,plain,(
% 1.89/0.62    ! [X0] : (((v7_lattices(X0) | (((k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).
% 1.89/0.62  fof(f31,plain,(
% 1.89/0.62    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f32,plain,(
% 1.89/0.62    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f33,plain,(
% 1.89/0.62    ! [X0] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f30,plain,(
% 1.89/0.62    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(rectify,[],[f29])).
% 1.89/0.62  fof(f29,plain,(
% 1.89/0.62    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(nnf_transformation,[],[f17])).
% 1.89/0.62  fof(f17,plain,(
% 1.89/0.62    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(flattening,[],[f16])).
% 1.89/0.62  fof(f16,plain,(
% 1.89/0.62    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f2])).
% 1.89/0.62  fof(f2,axiom,(
% 1.89/0.62    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3))))))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattices)).
% 1.89/0.62  fof(f89,plain,(
% 1.89/0.62    ( ! [X0,X1] : (r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f88,f44])).
% 1.89/0.62  fof(f88,plain,(
% 1.89/0.62    ( ! [X0,X1] : (r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 1.89/0.62    inference(resolution,[],[f87,f50])).
% 1.89/0.62  fof(f87,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~l1_lattices(sK0) | r1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f86,f40])).
% 1.89/0.62  fof(f86,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.89/0.62    inference(duplicate_literal_removal,[],[f85])).
% 1.89/0.62  fof(f85,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.89/0.62    inference(resolution,[],[f84,f65])).
% 1.89/0.62  fof(f84,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(k2_lattices(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f83,f44])).
% 1.89/0.62  fof(f83,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,X1,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 1.89/0.62    inference(resolution,[],[f82,f51])).
% 1.89/0.62  fof(f51,plain,(
% 1.89/0.62    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f11])).
% 1.89/0.62  fof(f82,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~l2_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f80,f40])).
% 1.89/0.62  fof(f80,plain,(
% 1.89/0.62    ( ! [X0,X1] : (r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(trivial_inequality_removal,[],[f79])).
% 1.89/0.62  fof(f79,plain,(
% 1.89/0.62    ( ! [X0,X1] : (X1 != X1 | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(duplicate_literal_removal,[],[f78])).
% 1.89/0.62  fof(f78,plain,(
% 1.89/0.62    ( ! [X0,X1] : (X1 != X1 | r1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_lattices(sK0,X0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(superposition,[],[f53,f76])).
% 1.89/0.62  fof(f76,plain,(
% 1.89/0.62    ( ! [X0,X1] : (k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f75,f40])).
% 1.89/0.62  fof(f75,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0 | v2_struct_0(sK0)) )),
% 1.89/0.62    inference(subsumption_resolution,[],[f74,f44])).
% 1.89/0.62  fof(f74,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X1,X0),X0) = X0 | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.89/0.62    inference(resolution,[],[f61,f42])).
% 1.89/0.62  fof(f61,plain,(
% 1.89/0.62    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f39])).
% 1.89/0.62  fof(f39,plain,(
% 1.89/0.62    ! [X0] : (((v8_lattices(X0) | ((sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0)) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f36,f38,f37])).
% 1.89/0.62  fof(f37,plain,(
% 1.89/0.62    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f38,plain,(
% 1.89/0.62    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0)) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 1.89/0.62    introduced(choice_axiom,[])).
% 1.89/0.62  fof(f36,plain,(
% 1.89/0.62    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(rectify,[],[f35])).
% 1.89/0.62  fof(f35,plain,(
% 1.89/0.62    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(nnf_transformation,[],[f19])).
% 1.89/0.62  fof(f19,plain,(
% 1.89/0.62    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(flattening,[],[f18])).
% 1.89/0.62  fof(f18,plain,(
% 1.89/0.62    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f3])).
% 1.89/0.62  fof(f3,axiom,(
% 1.89/0.62    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 1.89/0.62  fof(f53,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f27])).
% 1.89/0.62  fof(f27,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(nnf_transformation,[],[f13])).
% 1.89/0.62  fof(f13,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.89/0.62    inference(flattening,[],[f12])).
% 1.89/0.62  fof(f12,plain,(
% 1.89/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f1])).
% 1.89/0.62  fof(f1,axiom,(
% 1.89/0.62    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 1.89/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 1.89/0.62  % SZS output end Proof for theBenchmark
% 1.89/0.62  % (23188)------------------------------
% 1.89/0.62  % (23188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (23188)Termination reason: Refutation
% 1.89/0.62  
% 1.89/0.62  % (23188)Memory used [KB]: 7036
% 1.89/0.62  % (23188)Time elapsed: 0.189 s
% 1.89/0.62  % (23188)------------------------------
% 1.89/0.62  % (23188)------------------------------
% 1.89/0.62  % (23168)Success in time 0.261 s
%------------------------------------------------------------------------------
