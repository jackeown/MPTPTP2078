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
% DateTime   : Thu Dec  3 13:10:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 (4929 expanded)
%              Number of leaves         :   21 (2198 expanded)
%              Depth                    :   19
%              Number of atoms          :  592 (45625 expanded)
%              Number of equality atoms :  170 (16231 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f620,plain,(
    $false ),
    inference(global_subsumption,[],[f77,f619])).

fof(f619,plain,(
    sK2 = sK3 ),
    inference(backward_demodulation,[],[f382,f615])).

fof(f615,plain,(
    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) ),
    inference(backward_demodulation,[],[f594,f608])).

fof(f608,plain,(
    sK3 = k4_lattices(sK0,sK3,sK3) ),
    inference(backward_demodulation,[],[f366,f607])).

fof(f607,plain,(
    sK3 = k2_lattices(sK0,sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f68,f115,f116,f71,f74,f74,f601,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f601,plain,(
    r1_lattices(sK0,sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f68,f111,f74,f74,f276,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f29])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f276,plain,(
    sK3 = k1_lattices(sK0,sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f68,f114,f115,f116,f71,f74,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

fof(f114,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f68,f69,f71,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f69,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( sK2 != sK3
    & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)
    & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v11_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f47,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                    & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3)
                  & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v11_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3)
                & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3)
              & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( X2 != X3
            & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3)
            & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( sK2 != X3
          & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2)
          & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X3] :
        ( sK2 != X3
        & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2)
        & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( sK2 != sK3
      & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)
      & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
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
                   => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                        & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                     => X2 = X3 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
                 => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                      & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                   => X2 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_lattices)).

fof(f111,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f71,f79])).

fof(f79,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f74,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f116,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f68,f69,f71,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f115,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f68,f69,f71,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f366,plain,(
    k2_lattices(sK0,sK3,sK3) = k4_lattices(sK0,sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f74,f74,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f110,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f71,f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f594,plain,(
    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) ),
    inference(backward_demodulation,[],[f589,f592])).

fof(f592,plain,(
    sK2 = k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f591,f203])).

fof(f203,plain,(
    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f177,f197])).

fof(f197,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f73,f109])).

fof(f73,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f177,plain,(
    sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f68,f71,f115,f72,f73,f101])).

fof(f101,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK11(X0) != k1_lattices(X0,k2_lattices(X0,sK10(X0),sK11(X0)),sK11(X0))
            & m1_subset_1(sK11(X0),u1_struct_0(X0))
            & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f64,f66,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK10(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK10(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK11(X0) != k1_lattices(X0,k2_lattices(X0,sK10(X0),sK11(X0)),sK11(X0))
        & m1_subset_1(sK11(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f33])).

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
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f591,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f582,f581])).

fof(f581,plain,(
    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f210,f578])).

fof(f578,plain,(
    sK2 = k4_lattices(sK0,sK2,sK2) ),
    inference(backward_demodulation,[],[f198,f577])).

fof(f577,plain,(
    sK2 = k2_lattices(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f68,f115,f116,f71,f73,f73,f571,f86])).

fof(f571,plain,(
    r1_lattices(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f68,f111,f73,f73,f150,f95])).

fof(f150,plain,(
    sK2 = k1_lattices(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f68,f114,f115,f116,f71,f73,f88])).

fof(f198,plain,(
    k2_lattices(sK0,sK2,sK2) = k4_lattices(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f73,f73,f109])).

fof(f210,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f209,f201])).

fof(f201,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f183,f181])).

fof(f181,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f73,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f112,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f68,f69,f71,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f183,plain,(
    k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f73,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f209,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f208,f198])).

fof(f208,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f173,f199])).

fof(f199,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f195,f193])).

fof(f193,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f73,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f195,plain,(
    k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f73,f109])).

fof(f173,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k2_lattices(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f68,f71,f70,f72,f73,f73,f96])).

fof(f96,plain,(
    ! [X6,X4,X0,X5] :
      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0)))
            & m1_subset_1(sK9(X0),u1_struct_0(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f58,f61,f60,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0)))
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).

fof(f70,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f582,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f213,f578])).

fof(f213,plain,(
    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK2)) ),
    inference(forward_demodulation,[],[f212,f185])).

fof(f185,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f73,f106])).

fof(f212,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK2)) ),
    inference(forward_demodulation,[],[f211,f199])).

fof(f211,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k4_lattices(sK0,sK2,sK2)) ),
    inference(forward_demodulation,[],[f172,f198])).

fof(f172,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f68,f71,f70,f73,f72,f73,f96])).

fof(f589,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f438,f581])).

fof(f438,plain,(
    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) ),
    inference(backward_demodulation,[],[f405,f436])).

fof(f436,plain,(
    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f402,f435])).

fof(f435,plain,(
    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f434,f378])).

fof(f378,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK3,sK1) ),
    inference(backward_demodulation,[],[f343,f377])).

fof(f377,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f340,f76])).

fof(f76,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f340,plain,(
    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f74,f105])).

fof(f343,plain,(
    k1_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f74,f106])).

fof(f434,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f433,f365])).

fof(f365,plain,(
    k2_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f73,f74,f109])).

fof(f433,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f314,f199])).

fof(f314,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k2_lattices(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f68,f71,f70,f73,f72,f74,f96])).

fof(f402,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f401,f201])).

fof(f401,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f400,f368])).

fof(f368,plain,(
    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f362,f359])).

fof(f359,plain,(
    k4_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f73,f74,f108])).

fof(f362,plain,(
    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f73,f74,f109])).

fof(f400,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f325,f370])).

fof(f370,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK3,sK1) ),
    inference(backward_demodulation,[],[f361,f369])).

fof(f369,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f358,f75])).

fof(f75,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f358,plain,(
    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f74,f108])).

fof(f361,plain,(
    k2_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f74,f109])).

fof(f325,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f68,f71,f70,f72,f73,f74,f96])).

fof(f405,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) ),
    inference(forward_demodulation,[],[f404,f375])).

fof(f375,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK3) ),
    inference(forward_demodulation,[],[f346,f76])).

fof(f346,plain,(
    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f74,f106])).

fof(f404,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) ),
    inference(forward_demodulation,[],[f403,f370])).

fof(f403,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k4_lattices(sK0,sK3,sK3)) ),
    inference(forward_demodulation,[],[f324,f366])).

fof(f324,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK3)) ),
    inference(unit_resulting_resolution,[],[f68,f71,f70,f74,f72,f74,f96])).

fof(f382,plain,(
    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f334,f367])).

fof(f367,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK3) ),
    inference(forward_demodulation,[],[f364,f75])).

fof(f364,plain,(
    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f74,f109])).

fof(f334,plain,(
    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3) ),
    inference(unit_resulting_resolution,[],[f68,f71,f115,f72,f74,f101])).

fof(f77,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (23115)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (23115)Refutation not found, incomplete strategy% (23115)------------------------------
% 0.21/0.47  % (23115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23127)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (23115)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (23115)Memory used [KB]: 10618
% 0.21/0.47  % (23115)Time elapsed: 0.059 s
% 0.21/0.47  % (23115)------------------------------
% 0.21/0.47  % (23115)------------------------------
% 0.21/0.48  % (23127)Refutation not found, incomplete strategy% (23127)------------------------------
% 0.21/0.48  % (23127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23127)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (23127)Memory used [KB]: 6140
% 0.21/0.48  % (23127)Time elapsed: 0.004 s
% 0.21/0.48  % (23127)------------------------------
% 0.21/0.48  % (23127)------------------------------
% 0.21/0.48  % (23136)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (23135)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (23136)Refutation not found, incomplete strategy% (23136)------------------------------
% 0.21/0.49  % (23136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23136)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (23136)Memory used [KB]: 10618
% 0.21/0.49  % (23136)Time elapsed: 0.059 s
% 0.21/0.49  % (23136)------------------------------
% 0.21/0.49  % (23136)------------------------------
% 0.21/0.49  % (23119)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (23129)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (23118)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (23126)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (23128)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (23121)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (23126)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f620,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(global_subsumption,[],[f77,f619])).
% 0.21/0.50  fof(f619,plain,(
% 0.21/0.50    sK2 = sK3),
% 0.21/0.50    inference(backward_demodulation,[],[f382,f615])).
% 0.21/0.50  fof(f615,plain,(
% 0.21/0.50    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f594,f608])).
% 0.21/0.50  fof(f608,plain,(
% 0.21/0.50    sK3 = k4_lattices(sK0,sK3,sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f366,f607])).
% 0.21/0.50  fof(f607,plain,(
% 0.21/0.50    sK3 = k2_lattices(sK0,sK3,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f115,f116,f71,f74,f74,f601,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 0.21/0.50  fof(f601,plain,(
% 0.21/0.50    r1_lattices(sK0,sK3,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f111,f74,f74,f276,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    sK3 = k1_lattices(sK0,sK3,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f115,f116,f71,f74,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    v6_lattices(sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f69,f71,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    v10_lattices(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    (((sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f47,f46,f45,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3) & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3) & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (sK2 != X3 & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2) & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ? [X3] : (sK2 != X3 & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2) & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_lattices)).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    l2_lattices(sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f71,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    l3_lattices(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    v9_lattices(sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f69,f71,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    v8_lattices(sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f69,f71,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,sK3) = k4_lattices(sK0,sK3,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f74,f74,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    l1_lattices(sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f71,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f594,plain,(
% 0.21/0.50    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3))),
% 0.21/0.50    inference(backward_demodulation,[],[f589,f592])).
% 0.21/0.50  fof(f592,plain,(
% 0.21/0.50    sK2 = k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f591,f203])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f177,f197])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f73,f109])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f71,f115,f72,f73,f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ! [X0] : (((v8_lattices(X0) | ((sK11(X0) != k1_lattices(X0,k2_lattices(X0,sK10(X0),sK11(X0)),sK11(X0)) & m1_subset_1(sK11(X0),u1_struct_0(X0))) & m1_subset_1(sK10(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f64,f66,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK10(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK10(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK10(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK11(X0) != k1_lattices(X0,k2_lattices(X0,sK10(X0),sK11(X0)),sK11(X0)) & m1_subset_1(sK11(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
% 0.21/0.50  fof(f591,plain,(
% 0.21/0.50    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f582,f581])).
% 0.21/0.50  fof(f581,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f210,f578])).
% 0.21/0.50  fof(f578,plain,(
% 0.21/0.50    sK2 = k4_lattices(sK0,sK2,sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f198,f577])).
% 0.21/0.50  fof(f577,plain,(
% 0.21/0.50    sK2 = k2_lattices(sK0,sK2,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f115,f116,f71,f73,f73,f571,f86])).
% 0.21/0.50  fof(f571,plain,(
% 0.21/0.50    r1_lattices(sK0,sK2,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f111,f73,f73,f150,f95])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    sK2 = k1_lattices(sK0,sK2,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f115,f116,f71,f73,f88])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,sK2) = k4_lattices(sK0,sK2,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f73,f73,f109])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f209,f201])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f183,f181])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f73,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    v4_lattices(sK0)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f69,f71,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK2,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f73,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f208,f198])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f173,f199])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f195,f193])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f73,f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f73,f109])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),k2_lattices(sK0,sK2,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f71,f70,f72,f73,f73,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X6,X4,X0,X5] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ! [X0] : (((v11_lattices(X0) | (((k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f58,f61,f60,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ! [X0] : (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    v11_lattices(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f582,plain,(
% 0.21/0.50    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f213,f578])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f212,f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f73,f106])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f211,f199])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k4_lattices(sK0,sK2,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f172,f198])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,sK2))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f71,f70,f73,f72,f73,f96])).
% 0.21/0.50  fof(f589,plain,(
% 0.21/0.50    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) = k1_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f438,f581])).
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3))),
% 0.21/0.50    inference(backward_demodulation,[],[f405,f436])).
% 0.21/0.50  fof(f436,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f402,f435])).
% 0.21/0.50  fof(f435,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f434,f378])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f343,f377])).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(forward_demodulation,[],[f340,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f74,f105])).
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    k1_lattices(sK0,sK3,sK1) = k3_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f74,f106])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f433,f365])).
% 0.21/0.50  fof(f365,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK2,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f73,f74,f109])).
% 0.21/0.50  fof(f433,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f314,f199])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k2_lattices(sK0,sK2,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f71,f70,f73,f72,f74,f96])).
% 0.21/0.50  fof(f402,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f401,f201])).
% 0.21/0.50  fof(f401,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f400,f368])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3)),
% 0.21/0.50    inference(backward_demodulation,[],[f362,f359])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    k4_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f73,f74,f108])).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK3,sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f73,f74,f109])).
% 0.21/0.50  fof(f400,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK1,sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f325,f370])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f361,f369])).
% 0.21/0.50  fof(f369,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(forward_demodulation,[],[f358,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f74,f108])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,sK1) = k4_lattices(sK0,sK3,sK1)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f74,f109])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f71,f70,f72,f73,f74,f96])).
% 0.21/0.50  fof(f405,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f404,f375])).
% 0.21/0.50  fof(f375,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(forward_demodulation,[],[f346,f76])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f112,f111,f72,f74,f106])).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f403,f370])).
% 0.21/0.50  fof(f403,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k4_lattices(sK0,sK3,sK3))),
% 0.21/0.50    inference(forward_demodulation,[],[f324,f366])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,sK3))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f71,f70,f74,f72,f74,f96])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)),
% 0.21/0.50    inference(forward_demodulation,[],[f334,f367])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(forward_demodulation,[],[f364,f75])).
% 0.21/0.50  fof(f364,plain,(
% 0.21/0.50    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f114,f110,f72,f74,f109])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f68,f71,f115,f72,f74,f101])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    sK2 != sK3),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (23126)------------------------------
% 0.21/0.50  % (23126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23126)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (23126)Memory used [KB]: 11001
% 0.21/0.50  % (23126)Time elapsed: 0.076 s
% 0.21/0.50  % (23126)------------------------------
% 0.21/0.50  % (23126)------------------------------
% 0.21/0.50  % (23116)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (23105)Success in time 0.143 s
%------------------------------------------------------------------------------
