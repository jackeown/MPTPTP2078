%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 (2470 expanded)
%              Number of leaves         :   17 (1092 expanded)
%              Depth                    :   18
%              Number of atoms          :  476 (22795 expanded)
%              Number of equality atoms :  125 (8097 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(subsumption_resolution,[],[f467,f55])).

fof(f55,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f39,f38,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).

fof(f467,plain,(
    sK2 = sK3 ),
    inference(backward_demodulation,[],[f459,f466])).

fof(f466,plain,(
    sK2 = k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f411,f171])).

fof(f171,plain,(
    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f150,f136])).

fof(f136,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f128,f134])).

fof(f134,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f80,f79,f50,f51,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f51,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f49,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f46,f47,f49,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f47,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f128,plain,(
    k3_lattices(sK0,sK2,sK1) = k1_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f80,f79,f50,f51,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f150,plain,(
    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f49,f50,f51,f83,f65])).

fof(f65,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f44,f43])).

fof(f43,plain,(
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

fof(f44,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0)))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(f83,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f46,f47,f49,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f411,plain,(
    k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f81,f78,f51,f126,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f126,plain,(
    m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f46,f80,f79,f50,f51,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).

fof(f78,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f49,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f46,f47,f49,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f459,plain,(
    sK3 = k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f157,f458])).

fof(f458,plain,(
    sK3 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f457,f265])).

fof(f265,plain,(
    sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f211,f251])).

fof(f251,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f235,f247])).

fof(f247,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f244,f54])).

fof(f54,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f244,plain,(
    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f80,f79,f50,f52,f73])).

fof(f52,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f235,plain,(
    k3_lattices(sK0,sK3,sK1) = k1_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f80,f79,f50,f52,f72])).

fof(f211,plain,(
    sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f49,f83,f50,f52,f65])).

fof(f457,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f412,f328])).

fof(f328,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f296,f327])).

fof(f327,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f326,f122])).

fof(f122,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f81,f78,f50,f51,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f326,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f325,f301])).

fof(f301,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f300,f255])).

fof(f255,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f226,f53])).

fof(f53,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f226,plain,(
    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f81,f78,f50,f52,f70])).

fof(f300,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK3,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f195,f134])).

fof(f195,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK3,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f50,f51,f52,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v11_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_lattices)).

fof(f48,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f325,plain,(
    k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f324,f245])).

fof(f245,plain,(
    k3_lattices(sK0,sK3,sK2) = k3_lattices(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f46,f80,f79,f51,f52,f73])).

fof(f324,plain,(
    k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK2),k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f186,f247])).

fof(f186,plain,(
    k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK2),k3_lattices(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f50,f51,f52,f63])).

fof(f296,plain,(
    k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f295,f255])).

fof(f295,plain,(
    k3_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK1)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f294,f266])).

fof(f266,plain,(
    sK3 = k3_lattices(sK0,sK3,sK3) ),
    inference(backward_demodulation,[],[f240,f210])).

fof(f210,plain,(
    sK3 = k1_lattices(sK0,sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f46,f81,f82,f83,f49,f52,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k1_lattices(X0,X1,X1) = X1
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

fof(f82,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f46,f47,f49,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f240,plain,(
    k3_lattices(sK0,sK3,sK3) = k1_lattices(sK0,sK3,sK3) ),
    inference(unit_resulting_resolution,[],[f46,f80,f79,f52,f52,f72])).

fof(f294,plain,(
    k3_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f198,f247])).

fof(f198,plain,(
    k3_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f50,f52,f52,f63])).

fof(f412,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f46,f81,f78,f52,f126,f69])).

fof(f157,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f141,f156])).

fof(f156,plain,(
    sK2 = k3_lattices(sK0,sK2,sK2) ),
    inference(backward_demodulation,[],[f131,f153])).

fof(f153,plain,(
    sK2 = k1_lattices(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f46,f81,f82,f49,f51,f83,f64])).

fof(f131,plain,(
    k3_lattices(sK0,sK2,sK2) = k1_lattices(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f46,f80,f79,f51,f51,f72])).

fof(f141,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f140,f122])).

fof(f140,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f110,f134])).

fof(f110,plain,(
    k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f50,f51,f51,f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:54:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (15801)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (15798)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (15792)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (15785)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (15788)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (15792)Refutation not found, incomplete strategy% (15792)------------------------------
% 0.21/0.50  % (15792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15792)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15792)Memory used [KB]: 6396
% 0.21/0.50  % (15792)Time elapsed: 0.061 s
% 0.21/0.50  % (15792)------------------------------
% 0.21/0.50  % (15792)------------------------------
% 0.21/0.50  % (15789)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (15794)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (15794)Refutation not found, incomplete strategy% (15794)------------------------------
% 0.21/0.50  % (15794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15794)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15794)Memory used [KB]: 6012
% 0.21/0.50  % (15794)Time elapsed: 0.001 s
% 0.21/0.50  % (15794)------------------------------
% 0.21/0.50  % (15794)------------------------------
% 0.21/0.50  % (15797)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (15787)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (15786)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (15784)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (15782)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (15783)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (15800)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (15795)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (15793)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (15802)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (15802)Refutation not found, incomplete strategy% (15802)------------------------------
% 0.21/0.51  % (15802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15802)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15802)Memory used [KB]: 10618
% 0.21/0.51  % (15802)Time elapsed: 0.107 s
% 0.21/0.51  % (15802)------------------------------
% 0.21/0.51  % (15802)------------------------------
% 0.21/0.52  % (15790)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (15791)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (15797)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (15799)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % (15796)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f468,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f467,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    sK2 != sK3),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    (((sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f39,f38,f37,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v11_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,X1,X2) = k3_lattices(sK0,X1,X3) & k4_lattices(sK0,X1,X2) = k4_lattices(sK0,X1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3) & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : (X2 != X3 & k3_lattices(sK0,sK1,X2) = k3_lattices(sK0,sK1,X3) & k4_lattices(sK0,sK1,X2) = k4_lattices(sK0,sK1,X3) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (sK2 != X3 & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2) & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ? [X3] : (sK2 != X3 & k3_lattices(sK0,sK1,X3) = k3_lattices(sK0,sK1,sK2) & k4_lattices(sK0,sK1,X3) = k4_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (sK2 != sK3 & k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) & k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).
% 0.21/0.53  fof(f467,plain,(
% 0.21/0.53    sK2 = sK3),
% 0.21/0.53    inference(backward_demodulation,[],[f459,f466])).
% 0.21/0.53  fof(f466,plain,(
% 0.21/0.53    sK2 = k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f411,f171])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f150,f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f128,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f80,f79,f50,f51,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    l2_lattices(sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f49,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    l3_lattices(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    v4_lattices(sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f47,f49,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    v10_lattices(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,sK1) = k1_lattices(sK0,sK2,sK1)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f80,f79,f50,f51,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f49,f50,f51,f83,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X4,X0,X3] : (~v9_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X0] : (((v9_lattices(X0) | ((sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f44,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0] : (? [X2] : (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK4(X0) != k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(rectify,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    v9_lattices(sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f47,f49,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f411,plain,(
% 0.21/0.53    k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f81,f78,f51,f126,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f80,f79,f50,f51,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    l1_lattices(sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f49,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    v6_lattices(sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f47,f49,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f459,plain,(
% 0.21/0.53    sK3 = k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f157,f458])).
% 0.21/0.53  fof(f458,plain,(
% 0.21/0.53    sK3 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f457,f265])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f211,f251])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK3,sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f235,f247])).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f244,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f80,f79,f50,f52,f73])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    k3_lattices(sK0,sK3,sK1) = k1_lattices(sK0,sK3,sK1)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f80,f79,f50,f52,f72])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK1))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f49,f83,f50,f52,f65])).
% 0.21/0.53  fof(f457,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f412,f328])).
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f296,f327])).
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f326,f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f81,f78,f50,f51,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f325,f301])).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f300,f255])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1)),
% 0.21/0.53    inference(forward_demodulation,[],[f226,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f81,f78,f50,f52,f70])).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK3,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f195,f134])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK3,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK2,sK1))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f50,f51,f52,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v11_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_lattices)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    v11_lattices(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK3),k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f324,f245])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    k3_lattices(sK0,sK3,sK2) = k3_lattices(sK0,sK2,sK3)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f80,f79,f51,f52,f73])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK2),k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f186,f247])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    k3_lattices(sK0,sK3,k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK2),k3_lattices(sK0,sK3,sK1))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f50,f51,f52,f63])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f295,f255])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    k3_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK1)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f294,f266])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    sK3 = k3_lattices(sK0,sK3,sK3)),
% 0.21/0.53    inference(backward_demodulation,[],[f240,f210])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    sK3 = k1_lattices(sK0,sK3,sK3)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f81,f82,f83,f49,f52,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v9_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k1_lattices(X0,X1,X1) = X1 | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    v8_lattices(sK0)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f47,f49,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    k3_lattices(sK0,sK3,sK3) = k1_lattices(sK0,sK3,sK3)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f80,f79,f52,f52,f72])).
% 0.21/0.53  fof(f294,plain,(
% 0.21/0.53    k3_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f198,f247])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    k3_lattices(sK0,sK3,k4_lattices(sK0,sK3,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK3),k3_lattices(sK0,sK3,sK1))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f50,f52,f52,f63])).
% 0.21/0.53  fof(f412,plain,(
% 0.21/0.53    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f81,f78,f52,f126,f69])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f141,f156])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    sK2 = k3_lattices(sK0,sK2,sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f131,f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    sK2 = k1_lattices(sK0,sK2,sK2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f81,f82,f49,f51,f83,f64])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,sK2) = k1_lattices(sK0,sK2,sK2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f80,f79,f51,f51,f72])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f140,f122])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK1,sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f110,f134])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k4_lattices(sK0,sK2,sK1)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK2),k3_lattices(sK0,sK2,sK1))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f46,f47,f48,f49,f50,f51,f51,f63])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (15797)------------------------------
% 0.21/0.53  % (15797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15797)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (15797)Memory used [KB]: 6396
% 0.21/0.53  % (15797)Time elapsed: 0.113 s
% 0.21/0.53  % (15797)------------------------------
% 0.21/0.53  % (15797)------------------------------
% 0.21/0.53  % (15781)Success in time 0.172 s
%------------------------------------------------------------------------------
