%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:42 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 410 expanded)
%              Number of leaves         :   14 ( 120 expanded)
%              Depth                    :   28
%              Number of atoms          :  550 (2193 expanded)
%              Number of equality atoms :  109 ( 379 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f249])).

fof(f249,plain,(
    k6_lattices(sK0) != k6_lattices(sK0) ),
    inference(superposition,[],[f44,f248])).

fof(f248,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(resolution,[],[f246,f42])).

fof(f42,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v14_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v14_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_lattices)).

fof(f246,plain,
    ( ~ l3_lattices(sK0)
    | k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(resolution,[],[f245,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f245,plain,
    ( v2_struct_0(sK0)
    | k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f244,f46])).

fof(f46,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f244,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(forward_demodulation,[],[f243,f236])).

fof(f236,plain,(
    k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f228,f42])).

fof(f228,plain,
    ( ~ l3_lattices(sK0)
    | k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f227,f39])).

fof(f227,plain,
    ( v2_struct_0(sK0)
    | k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f224,f46])).

fof(f224,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f223,f203])).

fof(f203,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f159,f202])).

fof(f202,plain,(
    sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f201,f42])).

fof(f201,plain,
    ( ~ l3_lattices(sK0)
    | sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f200,f39])).

fof(f200,plain,
    ( v2_struct_0(sK0)
    | sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f199,f46])).

fof(f199,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(forward_demodulation,[],[f198,f74])).

fof(f74,plain,(
    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(resolution,[],[f68,f39])).

fof(f68,plain,
    ( v2_struct_0(sK0)
    | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(resolution,[],[f66,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,k6_lattices(sK0),X0) = X0
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f65,f42])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k4_lattices(sK0,k6_lattices(sK0),X0) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f64,f40])).

fof(f40,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | k4_lattices(sK0,k6_lattices(sK0),X0) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f54,f41])).

fof(f41,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v14_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

fof(f198,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ l2_lattices(sK0) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f186,f55])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f186,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X1) = k4_lattices(sK0,X1,sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f179,f43])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f155,f42])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f109,f40])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f85,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f159,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f127,f158])).

fof(f158,plain,(
    k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f157,f42])).

fof(f157,plain,
    ( ~ l3_lattices(sK0)
    | k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f156,f39])).

fof(f156,plain,
    ( v2_struct_0(sK0)
    | k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f152,f46])).

fof(f152,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,
    ( k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f140,f55])).

fof(f140,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,sK1,X1) = k4_lattices(sK0,sK1,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f138,f43])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k2_lattices(sK0,X1,X0) = k4_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f135,f42])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f91,f40])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f84,f50])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f60,f45])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f127,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0)) ),
    inference(resolution,[],[f121,f39])).

fof(f121,plain,
    ( v2_struct_0(sK0)
    | k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0)) ),
    inference(resolution,[],[f119,f43])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,X0,k6_lattices(sK0)),k6_lattices(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f118,f42])).

fof(f118,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,X0,k6_lattices(sK0)),k6_lattices(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f98,f46])).

fof(f98,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,X0,k6_lattices(sK0)),k6_lattices(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,X0,k6_lattices(sK0)),k6_lattices(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f89,f55])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1 ) ),
    inference(resolution,[],[f88,f42])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f77,f40])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f56,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK3(X0) != k1_lattices(X0,k2_lattices(X0,sK2(X0),sK3(X0)),sK3(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f37,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK2(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK2(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK3(X0) != k1_lattices(X0,k2_lattices(X0,sK2(X0),sK3(X0)),sK3(X0))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f223,plain,
    ( k1_lattices(sK0,sK1,k6_lattices(sK0)) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ l2_lattices(sK0) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,
    ( k1_lattices(sK0,sK1,k6_lattices(sK0)) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f211,f55])).

fof(f211,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k3_lattices(sK0,sK1,X1) = k1_lattices(sK0,sK1,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f184,f43])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f160,f42])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f117,f40])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f243,plain,
    ( k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ l2_lattices(sK0) ),
    inference(duplicate_literal_removal,[],[f237])).

fof(f237,plain,
    ( k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f230,f55])).

fof(f230,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k3_lattices(sK0,sK1,X1) = k3_lattices(sK0,X1,sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f205,f43])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f166,f42])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f129,f40])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f87,f48])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f44,plain,(
    k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 10:15:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.46  % (20977)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.46  % (20977)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % (20985)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f250,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(trivial_inequality_removal,[],[f249])).
% 0.19/0.47  fof(f249,plain,(
% 0.19/0.47    k6_lattices(sK0) != k6_lattices(sK0)),
% 0.19/0.47    inference(superposition,[],[f44,f248])).
% 0.19/0.47  fof(f248,plain,(
% 0.19/0.47    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.19/0.47    inference(resolution,[],[f246,f42])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    l3_lattices(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    (k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v14_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f32,f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v14_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ? [X1] : (k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) => (k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,negated_conjecture,(
% 0.19/0.47    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1)))),
% 0.19/0.47    inference(negated_conjecture,[],[f10])).
% 0.19/0.47  fof(f10,conjecture,(
% 0.19/0.47    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_lattices)).
% 0.19/0.47  fof(f246,plain,(
% 0.19/0.47    ~l3_lattices(sK0) | k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.19/0.47    inference(resolution,[],[f245,f39])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ~v2_struct_0(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f33])).
% 0.19/0.47  fof(f245,plain,(
% 0.19/0.47    v2_struct_0(sK0) | k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1) | ~l3_lattices(sK0)),
% 0.19/0.47    inference(resolution,[],[f244,f46])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.19/0.47  fof(f244,plain,(
% 0.19/0.47    ~l2_lattices(sK0) | v2_struct_0(sK0) | k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.19/0.47    inference(forward_demodulation,[],[f243,f236])).
% 0.19/0.47  fof(f236,plain,(
% 0.19/0.47    k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.19/0.47    inference(resolution,[],[f228,f42])).
% 0.19/0.47  fof(f228,plain,(
% 0.19/0.47    ~l3_lattices(sK0) | k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.19/0.47    inference(resolution,[],[f227,f39])).
% 0.19/0.47  fof(f227,plain,(
% 0.19/0.47    v2_struct_0(sK0) | k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0)) | ~l3_lattices(sK0)),
% 0.19/0.47    inference(resolution,[],[f224,f46])).
% 0.19/0.47  fof(f224,plain,(
% 0.19/0.47    ~l2_lattices(sK0) | v2_struct_0(sK0) | k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.19/0.47    inference(forward_demodulation,[],[f223,f203])).
% 0.19/0.47  fof(f203,plain,(
% 0.19/0.47    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.19/0.47    inference(backward_demodulation,[],[f159,f202])).
% 0.19/0.47  fof(f202,plain,(
% 0.19/0.47    sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.19/0.47    inference(resolution,[],[f201,f42])).
% 0.19/0.47  fof(f201,plain,(
% 0.19/0.47    ~l3_lattices(sK0) | sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.19/0.47    inference(resolution,[],[f200,f39])).
% 0.19/0.47  fof(f200,plain,(
% 0.19/0.47    v2_struct_0(sK0) | sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0)) | ~l3_lattices(sK0)),
% 0.19/0.47    inference(resolution,[],[f199,f46])).
% 0.19/0.47  fof(f199,plain,(
% 0.19/0.47    ~l2_lattices(sK0) | v2_struct_0(sK0) | sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.19/0.47    inference(forward_demodulation,[],[f198,f74])).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.19/0.47    inference(resolution,[],[f68,f39])).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    v2_struct_0(sK0) | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.19/0.47    inference(resolution,[],[f66,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.47    inference(cnf_transformation,[],[f33])).
% 0.19/0.47  fof(f66,plain,(
% 0.19/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,k6_lattices(sK0),X0) = X0 | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f65,f42])).
% 0.19/0.47  fof(f65,plain,(
% 0.19/0.47    ( ! [X0] : (~l3_lattices(sK0) | k4_lattices(sK0,k6_lattices(sK0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f64,f40])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    v10_lattices(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f33])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    ( ! [X0] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | k4_lattices(sK0,k6_lattices(sK0),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f54,f41])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    v14_lattices(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f33])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v14_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).
% 0.19/0.47  fof(f198,plain,(
% 0.19/0.47    k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0) | ~l2_lattices(sK0)),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f192])).
% 0.19/0.47  fof(f192,plain,(
% 0.19/0.47    k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.19/0.47    inference(resolution,[],[f186,f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).
% 0.19/0.47  fof(f186,plain,(
% 0.19/0.47    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X1) = k4_lattices(sK0,X1,sK1) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f179,f43])).
% 0.19/0.47  fof(f179,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(resolution,[],[f155,f42])).
% 0.19/0.47  fof(f155,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(resolution,[],[f109,f40])).
% 0.19/0.47  fof(f109,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v10_lattices(X1) | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f108])).
% 0.19/0.47  fof(f108,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.19/0.47    inference(resolution,[],[f85,f50])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.19/0.47    inference(flattening,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.19/0.47  fof(f85,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k4_lattices(X1,X2,X0) = k4_lattices(X1,X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.19/0.47    inference(resolution,[],[f61,f45])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.19/0.47  fof(f159,plain,(
% 0.19/0.47    k6_lattices(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0))),
% 0.19/0.47    inference(backward_demodulation,[],[f127,f158])).
% 0.19/0.47  fof(f158,plain,(
% 0.19/0.47    k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.19/0.47    inference(resolution,[],[f157,f42])).
% 0.19/0.47  fof(f157,plain,(
% 0.19/0.47    ~l3_lattices(sK0) | k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.19/0.47    inference(resolution,[],[f156,f39])).
% 0.19/0.47  fof(f156,plain,(
% 0.19/0.47    v2_struct_0(sK0) | k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0)) | ~l3_lattices(sK0)),
% 0.19/0.47    inference(resolution,[],[f152,f46])).
% 0.19/0.47  fof(f152,plain,(
% 0.19/0.47    ~l2_lattices(sK0) | v2_struct_0(sK0) | k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f146])).
% 0.19/0.47  fof(f146,plain,(
% 0.19/0.47    k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.19/0.47    inference(resolution,[],[f140,f55])).
% 0.19/0.47  fof(f140,plain,(
% 0.19/0.47    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,sK1,X1) = k4_lattices(sK0,sK1,X1) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f138,f43])).
% 0.19/0.47  fof(f138,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | k2_lattices(sK0,X1,X0) = k4_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(resolution,[],[f135,f42])).
% 0.19/0.47  fof(f135,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(resolution,[],[f91,f40])).
% 0.19/0.47  fof(f91,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v10_lattices(X1) | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f90])).
% 0.19/0.47  fof(f90,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | k4_lattices(X1,X0,X2) = k2_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.19/0.47    inference(resolution,[],[f84,f50])).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X2,X0) = k4_lattices(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.19/0.47    inference(resolution,[],[f60,f45])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.19/0.47  fof(f127,plain,(
% 0.19/0.47    k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0))),
% 0.19/0.47    inference(resolution,[],[f121,f39])).
% 0.19/0.47  fof(f121,plain,(
% 0.19/0.47    v2_struct_0(sK0) | k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK1,k6_lattices(sK0)),k6_lattices(sK0))),
% 0.19/0.47    inference(resolution,[],[f119,f43])).
% 0.19/0.47  fof(f119,plain,(
% 0.19/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,X0,k6_lattices(sK0)),k6_lattices(sK0)) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f118,f42])).
% 0.19/0.47  fof(f118,plain,(
% 0.19/0.47    ( ! [X0] : (~l3_lattices(sK0) | k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,X0,k6_lattices(sK0)),k6_lattices(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f98,f46])).
% 0.19/0.47  fof(f98,plain,(
% 0.19/0.47    ( ! [X0] : (~l2_lattices(sK0) | v2_struct_0(sK0) | k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,X0,k6_lattices(sK0)),k6_lattices(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f92])).
% 0.19/0.47  fof(f92,plain,(
% 0.19/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,X0,k6_lattices(sK0)),k6_lattices(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f89,f55])).
% 0.19/0.47  fof(f89,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1) )),
% 0.19/0.47    inference(resolution,[],[f88,f42])).
% 0.19/0.47  fof(f88,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~l3_lattices(sK0) | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(resolution,[],[f77,f40])).
% 0.19/0.47  fof(f77,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 | ~l3_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f76])).
% 0.19/0.47  fof(f76,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 | ~l3_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.19/0.47    inference(resolution,[],[f56,f52])).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f38])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ! [X0] : (((v8_lattices(X0) | ((sK3(X0) != k1_lattices(X0,k2_lattices(X0,sK2(X0),sK3(X0)),sK3(X0)) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f37,f36])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK2(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK2(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK3(X0) != k1_lattices(X0,k2_lattices(X0,sK2(X0),sK3(X0)),sK3(X0)) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(rectify,[],[f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(nnf_transformation,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 0.19/0.47  fof(f223,plain,(
% 0.19/0.47    k1_lattices(sK0,sK1,k6_lattices(sK0)) = k3_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0) | ~l2_lattices(sK0)),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f217])).
% 0.19/0.47  fof(f217,plain,(
% 0.19/0.47    k1_lattices(sK0,sK1,k6_lattices(sK0)) = k3_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.19/0.47    inference(resolution,[],[f211,f55])).
% 0.19/0.47  fof(f211,plain,(
% 0.19/0.47    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k3_lattices(sK0,sK1,X1) = k1_lattices(sK0,sK1,X1) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f184,f43])).
% 0.19/0.47  fof(f184,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(resolution,[],[f160,f42])).
% 0.19/0.47  fof(f160,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(resolution,[],[f117,f40])).
% 0.19/0.47  fof(f117,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v10_lattices(X1) | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f116])).
% 0.19/0.47  fof(f116,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.19/0.47    inference(resolution,[],[f86,f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f86,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v4_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.19/0.47    inference(resolution,[],[f62,f46])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.19/0.47  fof(f243,plain,(
% 0.19/0.47    k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0) | ~l2_lattices(sK0)),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f237])).
% 0.19/0.47  fof(f237,plain,(
% 0.19/0.47    k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.19/0.47    inference(resolution,[],[f230,f55])).
% 0.19/0.47  fof(f230,plain,(
% 0.19/0.47    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k3_lattices(sK0,sK1,X1) = k3_lattices(sK0,X1,sK1) | v2_struct_0(sK0)) )),
% 0.19/0.47    inference(resolution,[],[f205,f43])).
% 0.19/0.47  fof(f205,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(resolution,[],[f166,f42])).
% 0.19/0.47  fof(f166,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k3_lattices(sK0,X0,X1) = k3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.19/0.47    inference(resolution,[],[f129,f40])).
% 0.19/0.47  fof(f129,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v10_lattices(X1) | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f128])).
% 0.19/0.47  fof(f128,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.19/0.47    inference(resolution,[],[f87,f48])).
% 0.19/0.47  fof(f87,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v4_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k3_lattices(X1,X2,X0) = k3_lattices(X1,X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.19/0.47    inference(resolution,[],[f63,f46])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f33])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (20977)------------------------------
% 0.19/0.47  % (20977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (20977)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (20977)Memory used [KB]: 1791
% 0.19/0.47  % (20977)Time elapsed: 0.064 s
% 0.19/0.47  % (20977)------------------------------
% 0.19/0.47  % (20977)------------------------------
% 0.19/0.47  % (20967)Success in time 0.122 s
%------------------------------------------------------------------------------
