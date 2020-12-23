%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  177 (1829 expanded)
%              Number of leaves         :   10 ( 312 expanded)
%              Depth                    :   26
%              Number of atoms          :  581 (12530 expanded)
%              Number of equality atoms :  150 (3074 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(subsumption_resolution,[],[f391,f37])).

fof(f37,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f16])).

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

fof(f391,plain,(
    sK2 = sK3 ),
    inference(backward_demodulation,[],[f386,f390])).

fof(f390,plain,(
    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    inference(forward_demodulation,[],[f383,f213])).

fof(f213,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f163,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f163,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X1) = k2_lattices(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f162,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f162,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X1) = k2_lattices(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f161,f89])).

fof(f89,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f43,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f43,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f161,plain,(
    ! [X1] :
      ( ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X1) = k2_lattices(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f152,f74])).

fof(f74,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f73,f43])).

fof(f73,plain,
    ( ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f68,f40])).

fof(f68,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(resolution,[],[f41,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f41,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f152,plain,(
    ! [X1] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X1) = k2_lattices(sK0,sK1,X1) ) ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
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
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f383,plain,(
    sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) ),
    inference(resolution,[],[f172,f38])).

fof(f172,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK1,X5),X5) = X5 ) ),
    inference(subsumption_resolution,[],[f171,f76])).

fof(f76,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f75,f43])).

fof(f75,plain,
    ( ~ l3_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f69,f40])).

fof(f69,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f171,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK1,X5),X5) = X5
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f40])).

fof(f170,plain,(
    ! [X5] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK1,X5),X5) = X5
      | ~ v8_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f43])).

fof(f155,plain,(
    ! [X5] :
      ( ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,sK1,X5),X5) = X5
      | ~ v8_lattices(sK0) ) ),
    inference(resolution,[],[f39,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | ~ v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f386,plain,(
    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    inference(backward_demodulation,[],[f365,f385])).

fof(f385,plain,(
    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f382,f215])).

fof(f215,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK3) ),
    inference(forward_demodulation,[],[f212,f35])).

fof(f35,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f212,plain,(
    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3) ),
    inference(resolution,[],[f163,f34])).

fof(f34,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f382,plain,(
    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3) ),
    inference(resolution,[],[f172,f34])).

fof(f365,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    inference(backward_demodulation,[],[f317,f360])).

fof(f360,plain,(
    sK2 = k4_lattices(sK0,sK2,sK2) ),
    inference(backward_demodulation,[],[f199,f359])).

fof(f359,plain,(
    sK2 = k2_lattices(sK0,sK2,sK2) ),
    inference(forward_demodulation,[],[f356,f150])).

fof(f150,plain,(
    sK2 = k1_lattices(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f149,f40])).

fof(f149,plain,
    ( v2_struct_0(sK0)
    | sK2 = k1_lattices(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f148,f43])).

fof(f148,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2 = k1_lattices(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f147,f78])).

fof(f78,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f77,f43])).

fof(f77,plain,
    ( ~ l3_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f70,f40])).

fof(f70,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f147,plain,
    ( ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2 = k1_lattices(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f146,f76])).

fof(f146,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2 = k1_lattices(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f127,f74])).

fof(f127,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2 = k1_lattices(sK0,sK2,sK2) ),
    inference(resolution,[],[f38,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k1_lattices(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f356,plain,(
    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)) ),
    inference(resolution,[],[f145,f38])).

fof(f145,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,X6)) ) ),
    inference(subsumption_resolution,[],[f144,f78])).

fof(f144,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,X6))
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f40])).

fof(f143,plain,(
    ! [X6] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,X6))
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f126,f43])).

fof(f126,plain,(
    ! [X6] :
      ( ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,X6))
      | ~ v9_lattices(sK0) ) ),
    inference(resolution,[],[f38,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
      | ~ v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f199,plain,(
    k4_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,sK2) ),
    inference(resolution,[],[f133,f38])).

fof(f133,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X1) = k2_lattices(sK0,sK2,X1) ) ),
    inference(subsumption_resolution,[],[f132,f40])).

fof(f132,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X1) = k2_lattices(sK0,sK2,X1) ) ),
    inference(subsumption_resolution,[],[f131,f89])).

fof(f131,plain,(
    ! [X1] :
      ( ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X1) = k2_lattices(sK0,sK2,X1) ) ),
    inference(subsumption_resolution,[],[f122,f74])).

fof(f122,plain,(
    ! [X1] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X1) = k2_lattices(sK0,sK2,X1) ) ),
    inference(resolution,[],[f38,f45])).

fof(f317,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK2)) ),
    inference(forward_demodulation,[],[f316,f315])).

fof(f315,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f314,f298])).

fof(f298,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) ),
    inference(backward_demodulation,[],[f265,f297])).

fof(f297,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) ),
    inference(backward_demodulation,[],[f264,f290])).

fof(f290,plain,(
    sK3 = k4_lattices(sK0,sK3,sK3) ),
    inference(backward_demodulation,[],[f185,f289])).

fof(f289,plain,(
    sK3 = k2_lattices(sK0,sK3,sK3) ),
    inference(forward_demodulation,[],[f286,f120])).

fof(f120,plain,(
    sK3 = k1_lattices(sK0,sK3,sK3) ),
    inference(subsumption_resolution,[],[f119,f40])).

fof(f119,plain,
    ( v2_struct_0(sK0)
    | sK3 = k1_lattices(sK0,sK3,sK3) ),
    inference(subsumption_resolution,[],[f118,f43])).

fof(f118,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3 = k1_lattices(sK0,sK3,sK3) ),
    inference(subsumption_resolution,[],[f117,f78])).

fof(f117,plain,
    ( ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3 = k1_lattices(sK0,sK3,sK3) ),
    inference(subsumption_resolution,[],[f116,f76])).

fof(f116,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3 = k1_lattices(sK0,sK3,sK3) ),
    inference(subsumption_resolution,[],[f97,f74])).

fof(f97,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3 = k1_lattices(sK0,sK3,sK3) ),
    inference(resolution,[],[f34,f64])).

fof(f286,plain,(
    sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK3)) ),
    inference(resolution,[],[f115,f34])).

fof(f115,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,X6)) ) ),
    inference(subsumption_resolution,[],[f114,f78])).

fof(f114,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,X6))
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f40])).

fof(f113,plain,(
    ! [X6] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,X6))
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f96,f43])).

fof(f96,plain,(
    ! [X6] :
      ( ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,X6))
      | ~ v9_lattices(sK0) ) ),
    inference(resolution,[],[f34,f62])).

fof(f185,plain,(
    k4_lattices(sK0,sK3,sK3) = k2_lattices(sK0,sK3,sK3) ),
    inference(resolution,[],[f103,f34])).

fof(f103,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK3,X1) = k2_lattices(sK0,sK3,X1) ) ),
    inference(subsumption_resolution,[],[f102,f40])).

fof(f102,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK3,X1) = k2_lattices(sK0,sK3,X1) ) ),
    inference(subsumption_resolution,[],[f101,f89])).

fof(f101,plain,(
    ! [X1] :
      ( ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK3,X1) = k2_lattices(sK0,sK3,X1) ) ),
    inference(subsumption_resolution,[],[f92,f74])).

fof(f92,plain,(
    ! [X1] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,sK3,X1) = k2_lattices(sK0,sK3,X1) ) ),
    inference(resolution,[],[f34,f45])).

fof(f264,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) ),
    inference(forward_demodulation,[],[f263,f209])).

fof(f209,plain,(
    k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f208,f206])).

fof(f206,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f160,f38])).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X0) = k3_lattices(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f159,f40])).

fof(f159,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X0) = k3_lattices(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f158,f90])).

fof(f90,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f43,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f158,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X0) = k3_lattices(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f151,f72])).

fof(f72,plain,(
    v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f71,f43])).

fof(f71,plain,
    ( ~ l3_lattices(sK0)
    | v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f67,f40])).

fof(f67,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v4_lattices(sK0) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f151,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X0) = k3_lattices(sK0,sK1,X0) ) ),
    inference(resolution,[],[f39,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f208,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK3) ),
    inference(backward_demodulation,[],[f36,f205])).

fof(f205,plain,(
    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3) ),
    inference(resolution,[],[f160,f34])).

fof(f36,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f263,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3)) ),
    inference(forward_demodulation,[],[f260,f185])).

fof(f260,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK3,sK3)) ),
    inference(resolution,[],[f225,f34])).

fof(f225,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,X2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK3,X2)) ) ),
    inference(forward_demodulation,[],[f222,f193])).

fof(f193,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK3,sK1) ),
    inference(backward_demodulation,[],[f187,f192])).

fof(f192,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f190,f35])).

fof(f190,plain,(
    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1) ),
    inference(resolution,[],[f106,f39])).

fof(f106,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK3,X2) = k4_lattices(sK0,X2,sK3) ) ),
    inference(subsumption_resolution,[],[f105,f40])).

fof(f105,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK3,X2) = k4_lattices(sK0,X2,sK3) ) ),
    inference(subsumption_resolution,[],[f104,f89])).

fof(f104,plain,(
    ! [X2] :
      ( ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK3,X2) = k4_lattices(sK0,X2,sK3) ) ),
    inference(subsumption_resolution,[],[f93,f74])).

% (2307)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f93,plain,(
    ! [X2] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK3,X2) = k4_lattices(sK0,X2,sK3) ) ),
    inference(resolution,[],[f34,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f187,plain,(
    k4_lattices(sK0,sK3,sK1) = k2_lattices(sK0,sK3,sK1) ),
    inference(resolution,[],[f103,f39])).

fof(f222,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,X2)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,X2)) ) ),
    inference(resolution,[],[f109,f39])).

fof(f109,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_lattices(sK0,sK3,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK3,X3),k2_lattices(sK0,sK3,X4)) ) ),
    inference(subsumption_resolution,[],[f108,f42])).

fof(f42,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f108,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_lattices(sK0,sK3,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK3,X3),k2_lattices(sK0,sK3,X4))
      | ~ v11_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f107,f40])).

fof(f107,plain,(
    ! [X4,X3] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_lattices(sK0,sK3,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK3,X3),k2_lattices(sK0,sK3,X4))
      | ~ v11_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f43])).

fof(f94,plain,(
    ! [X4,X3] :
      ( ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_lattices(sK0,sK3,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK3,X3),k2_lattices(sK0,sK3,X4))
      | ~ v11_lattices(sK0) ) ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
      | ~ v11_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).

fof(f265,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f261,f191])).

fof(f191,plain,(
    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f186,f189])).

fof(f189,plain,(
    k4_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3) ),
    inference(resolution,[],[f106,f38])).

fof(f186,plain,(
    k4_lattices(sK0,sK3,sK2) = k2_lattices(sK0,sK3,sK2) ),
    inference(resolution,[],[f103,f38])).

fof(f261,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK3,sK2)) ),
    inference(resolution,[],[f225,f38])).

fof(f314,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f313,f209])).

fof(f313,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) ),
    inference(forward_demodulation,[],[f310,f198])).

fof(f198,plain,(
    k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK2,sK3) ),
    inference(resolution,[],[f133,f34])).

fof(f310,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK2,sK3)) ),
    inference(resolution,[],[f231,f34])).

fof(f231,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,X2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK2,X2)) ) ),
    inference(forward_demodulation,[],[f228,f204])).

fof(f204,plain,(
    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f200,f203])).

fof(f203,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    inference(resolution,[],[f136,f39])).

fof(f136,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X2) = k4_lattices(sK0,X2,sK2) ) ),
    inference(subsumption_resolution,[],[f135,f40])).

fof(f135,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X2) = k4_lattices(sK0,X2,sK2) ) ),
    inference(subsumption_resolution,[],[f134,f89])).

fof(f134,plain,(
    ! [X2] :
      ( ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X2) = k4_lattices(sK0,X2,sK2) ) ),
    inference(subsumption_resolution,[],[f123,f74])).

fof(f123,plain,(
    ! [X2] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k4_lattices(sK0,sK2,X2) = k4_lattices(sK0,X2,sK2) ) ),
    inference(resolution,[],[f38,f46])).

fof(f200,plain,(
    k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1) ),
    inference(resolution,[],[f133,f39])).

fof(f228,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,X2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,X2)) ) ),
    inference(resolution,[],[f139,f39])).

fof(f139,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_lattices(sK0,sK2,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK2,X3),k2_lattices(sK0,sK2,X4)) ) ),
    inference(subsumption_resolution,[],[f138,f42])).

fof(f138,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_lattices(sK0,sK2,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK2,X3),k2_lattices(sK0,sK2,X4))
      | ~ v11_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f40])).

fof(f137,plain,(
    ! [X4,X3] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_lattices(sK0,sK2,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK2,X3),k2_lattices(sK0,sK2,X4))
      | ~ v11_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f43])).

fof(f124,plain,(
    ! [X4,X3] :
      ( ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_lattices(sK0,sK2,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK2,X3),k2_lattices(sK0,sK2,X4))
      | ~ v11_lattices(sK0) ) ),
    inference(resolution,[],[f38,f47])).

fof(f316,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK2)) ),
    inference(forward_demodulation,[],[f311,f199])).

fof(f311,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK2,sK2)) ),
    inference(resolution,[],[f231,f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (2301)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (2293)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (2301)Refutation not found, incomplete strategy% (2301)------------------------------
% 0.20/0.49  % (2301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (2289)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (2293)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f392,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f391,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    sK2 != sK3),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f11])).
% 0.20/0.50  fof(f11,conjecture,(
% 0.20/0.50    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_lattices)).
% 0.20/0.50  fof(f391,plain,(
% 0.20/0.50    sK2 = sK3),
% 0.20/0.50    inference(backward_demodulation,[],[f386,f390])).
% 0.20/0.50  fof(f390,plain,(
% 0.20/0.50    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 0.20/0.50    inference(forward_demodulation,[],[f383,f213])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)),
% 0.20/0.50    inference(resolution,[],[f163,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X1) = k2_lattices(sK0,sK1,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f162,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X1) = k2_lattices(sK0,sK1,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f161,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    l1_lattices(sK0)),
% 0.20/0.50    inference(resolution,[],[f43,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    l3_lattices(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X1) = k2_lattices(sK0,sK1,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f152,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    v6_lattices(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f73,f43])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f68,f40])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.20/0.50    inference(resolution,[],[f41,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v6_lattices(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    v10_lattices(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ( ! [X1] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X1) = k2_lattices(sK0,sK1,X1)) )),
% 0.20/0.50    inference(resolution,[],[f39,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f383,plain,(
% 0.20/0.50    sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2)),
% 0.20/0.50    inference(resolution,[],[f172,f38])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK1,X5),X5) = X5) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f171,f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    v8_lattices(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f75,f43])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ~l3_lattices(sK0) | v8_lattices(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f69,f40])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~l3_lattices(sK0) | v8_lattices(sK0)),
% 0.20/0.50    inference(resolution,[],[f41,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v8_lattices(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK1,X5),X5) = X5 | ~v8_lattices(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f170,f40])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    ( ! [X5] : (v2_struct_0(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK1,X5),X5) = X5 | ~v8_lattices(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f155,f43])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    ( ! [X5] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,sK1,X5),X5) = X5 | ~v8_lattices(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f39,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~v8_lattices(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 0.20/0.50  fof(f386,plain,(
% 0.20/0.50    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f365,f385])).
% 0.20/0.50  fof(f385,plain,(
% 0.20/0.50    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)),
% 0.20/0.50    inference(forward_demodulation,[],[f382,f215])).
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK3)),
% 0.20/0.50    inference(forward_demodulation,[],[f212,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    k4_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,sK3)),
% 0.20/0.50    inference(resolution,[],[f163,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f382,plain,(
% 0.20/0.50    sK3 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),sK3)),
% 0.20/0.50    inference(resolution,[],[f172,f34])).
% 0.20/0.50  fof(f365,plain,(
% 0.20/0.50    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f317,f360])).
% 0.20/0.50  fof(f360,plain,(
% 0.20/0.50    sK2 = k4_lattices(sK0,sK2,sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f199,f359])).
% 0.20/0.50  fof(f359,plain,(
% 0.20/0.50    sK2 = k2_lattices(sK0,sK2,sK2)),
% 0.20/0.50    inference(forward_demodulation,[],[f356,f150])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    sK2 = k1_lattices(sK0,sK2,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f149,f40])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    v2_struct_0(sK0) | sK2 = k1_lattices(sK0,sK2,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f148,f43])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2 = k1_lattices(sK0,sK2,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f147,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    v9_lattices(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f77,f43])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ~l3_lattices(sK0) | v9_lattices(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f70,f40])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~l3_lattices(sK0) | v9_lattices(sK0)),
% 0.20/0.50    inference(resolution,[],[f41,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2 = k1_lattices(sK0,sK2,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f146,f76])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2 = k1_lattices(sK0,sK2,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f127,f74])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2 = k1_lattices(sK0,sK2,sK2)),
% 0.20/0.50    inference(resolution,[],[f38,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k1_lattices(X0,X1,X1) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).
% 0.20/0.50  fof(f356,plain,(
% 0.20/0.50    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2))),
% 0.20/0.50    inference(resolution,[],[f145,f38])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,X6))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f144,f78])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,X6)) | ~v9_lattices(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f143,f40])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    ( ! [X6] : (v2_struct_0(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,X6)) | ~v9_lattices(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f126,f43])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ( ! [X6] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,X6)) | ~v9_lattices(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f38,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~v9_lattices(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    k4_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,sK2)),
% 0.20/0.50    inference(resolution,[],[f133,f38])).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X1) = k2_lattices(sK0,sK2,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f132,f40])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X1) = k2_lattices(sK0,sK2,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f131,f89])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X1) = k2_lattices(sK0,sK2,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f122,f74])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ( ! [X1] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X1) = k2_lattices(sK0,sK2,X1)) )),
% 0.20/0.50    inference(resolution,[],[f38,f45])).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f316,f315])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f314,f298])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)),
% 0.20/0.50    inference(backward_demodulation,[],[f265,f297])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)),
% 0.20/0.50    inference(backward_demodulation,[],[f264,f290])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    sK3 = k4_lattices(sK0,sK3,sK3)),
% 0.20/0.50    inference(backward_demodulation,[],[f185,f289])).
% 0.20/0.50  fof(f289,plain,(
% 0.20/0.50    sK3 = k2_lattices(sK0,sK3,sK3)),
% 0.20/0.50    inference(forward_demodulation,[],[f286,f120])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    sK3 = k1_lattices(sK0,sK3,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f119,f40])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    v2_struct_0(sK0) | sK3 = k1_lattices(sK0,sK3,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f118,f43])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3 = k1_lattices(sK0,sK3,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f117,f78])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3 = k1_lattices(sK0,sK3,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f116,f76])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3 = k1_lattices(sK0,sK3,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f97,f74])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3 = k1_lattices(sK0,sK3,sK3)),
% 0.20/0.50    inference(resolution,[],[f34,f64])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK3))),
% 0.20/0.50    inference(resolution,[],[f115,f34])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,X6))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f114,f78])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,X6)) | ~v9_lattices(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f113,f40])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ( ! [X6] : (v2_struct_0(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,X6)) | ~v9_lattices(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f96,f43])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X6] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,X6)) | ~v9_lattices(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f34,f62])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    k4_lattices(sK0,sK3,sK3) = k2_lattices(sK0,sK3,sK3)),
% 0.20/0.50    inference(resolution,[],[f103,f34])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK3,X1) = k2_lattices(sK0,sK3,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f102,f40])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK3,X1) = k2_lattices(sK0,sK3,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f101,f89])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK3,X1) = k2_lattices(sK0,sK3,X1)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f92,f74])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ( ! [X1] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,sK3,X1) = k2_lattices(sK0,sK3,X1)) )),
% 0.20/0.50    inference(resolution,[],[f34,f45])).
% 0.20/0.50  fof(f264,plain,(
% 0.20/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3))),
% 0.20/0.50    inference(forward_demodulation,[],[f263,f209])).
% 0.20/0.50  fof(f209,plain,(
% 0.20/0.50    k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.50    inference(backward_demodulation,[],[f208,f206])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.50    inference(resolution,[],[f160,f38])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X0) = k3_lattices(sK0,sK1,X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f159,f40])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X0) = k3_lattices(sK0,sK1,X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f158,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    l2_lattices(sK0)),
% 0.20/0.50    inference(resolution,[],[f43,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    ( ! [X0] : (~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X0) = k3_lattices(sK0,sK1,X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f151,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    v4_lattices(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f71,f43])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ~l3_lattices(sK0) | v4_lattices(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f67,f40])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~l3_lattices(sK0) | v4_lattices(sK0)),
% 0.20/0.50    inference(resolution,[],[f41,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v4_lattices(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    ( ! [X0] : (~v4_lattices(sK0) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X0) = k3_lattices(sK0,sK1,X0)) )),
% 0.20/0.50    inference(resolution,[],[f39,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v4_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK3)),
% 0.20/0.50    inference(backward_demodulation,[],[f36,f205])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    k3_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK1,sK3)),
% 0.20/0.50    inference(resolution,[],[f160,f34])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK3,sK3))),
% 0.20/0.50    inference(forward_demodulation,[],[f260,f185])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK3,sK3))),
% 0.20/0.50    inference(resolution,[],[f225,f34])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,X2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK3,X2))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f222,f193])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK3,sK1)),
% 0.20/0.50    inference(backward_demodulation,[],[f187,f192])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1)),
% 0.20/0.50    inference(forward_demodulation,[],[f190,f35])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1)),
% 0.20/0.50    inference(resolution,[],[f106,f39])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k4_lattices(sK0,sK3,X2) = k4_lattices(sK0,X2,sK3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f105,f40])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X2] : (v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k4_lattices(sK0,sK3,X2) = k4_lattices(sK0,X2,sK3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f104,f89])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ( ! [X2] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k4_lattices(sK0,sK3,X2) = k4_lattices(sK0,X2,sK3)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f93,f74])).
% 0.20/0.50  % (2307)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X2] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k4_lattices(sK0,sK3,X2) = k4_lattices(sK0,X2,sK3)) )),
% 0.20/0.50    inference(resolution,[],[f34,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    k4_lattices(sK0,sK3,sK1) = k2_lattices(sK0,sK3,sK1)),
% 0.20/0.50    inference(resolution,[],[f103,f39])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,X2)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK1),k2_lattices(sK0,sK3,X2))) )),
% 0.20/0.50    inference(resolution,[],[f109,f39])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,sK3,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK3,X3),k2_lattices(sK0,sK3,X4))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f108,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    v11_lattices(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,sK3,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK3,X3),k2_lattices(sK0,sK3,X4)) | ~v11_lattices(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f40])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    ( ! [X4,X3] : (v2_struct_0(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,sK3,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK3,X3),k2_lattices(sK0,sK3,X4)) | ~v11_lattices(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f94,f43])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X4,X3] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,sK3,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK3,X3),k2_lattices(sK0,sK3,X4)) | ~v11_lattices(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f34,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~v11_lattices(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattices)).
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3))),
% 0.20/0.50    inference(forward_demodulation,[],[f261,f191])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    k2_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3)),
% 0.20/0.50    inference(backward_demodulation,[],[f186,f189])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    k4_lattices(sK0,sK3,sK2) = k4_lattices(sK0,sK2,sK3)),
% 0.20/0.50    inference(resolution,[],[f106,f38])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    k4_lattices(sK0,sK3,sK2) = k2_lattices(sK0,sK3,sK2)),
% 0.20/0.50    inference(resolution,[],[f103,f38])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    k2_lattices(sK0,sK3,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK3,sK2))),
% 0.20/0.50    inference(resolution,[],[f225,f38])).
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f313,f209])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK3)) = k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3))),
% 0.20/0.50    inference(forward_demodulation,[],[f310,f198])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK2,sK3)),
% 0.20/0.50    inference(resolution,[],[f133,f34])).
% 0.20/0.50  fof(f310,plain,(
% 0.20/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK2,sK3))),
% 0.20/0.50    inference(resolution,[],[f231,f34])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,X2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK2,X2))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f228,f204])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)),
% 0.20/0.50    inference(backward_demodulation,[],[f200,f203])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 0.20/0.50    inference(resolution,[],[f136,f39])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X2) = k4_lattices(sK0,X2,sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f135,f40])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ( ! [X2] : (v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X2) = k4_lattices(sK0,X2,sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f134,f89])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ( ! [X2] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X2) = k4_lattices(sK0,X2,sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f123,f74])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    ( ! [X2] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k4_lattices(sK0,sK2,X2) = k4_lattices(sK0,X2,sK2)) )),
% 0.20/0.50    inference(resolution,[],[f38,f46])).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1)),
% 0.20/0.50    inference(resolution,[],[f133,f39])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,X2)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),k2_lattices(sK0,sK2,X2))) )),
% 0.20/0.50    inference(resolution,[],[f139,f39])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,sK2,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK2,X3),k2_lattices(sK0,sK2,X4))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f138,f42])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,sK2,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK2,X3),k2_lattices(sK0,sK2,X4)) | ~v11_lattices(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f137,f40])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    ( ! [X4,X3] : (v2_struct_0(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,sK2,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK2,X3),k2_lattices(sK0,sK2,X4)) | ~v11_lattices(sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f124,f43])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ( ! [X4,X3] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,sK2,k1_lattices(sK0,X3,X4)) = k1_lattices(sK0,k2_lattices(sK0,sK2,X3),k2_lattices(sK0,sK2,X4)) | ~v11_lattices(sK0)) )),
% 0.20/0.50    inference(resolution,[],[f38,f47])).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,sK2,sK2))),
% 0.20/0.50    inference(forward_demodulation,[],[f311,f199])).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    k2_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),k2_lattices(sK0,sK2,sK2))),
% 0.20/0.50    inference(resolution,[],[f231,f38])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (2293)------------------------------
% 0.20/0.50  % (2293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2293)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (2293)Memory used [KB]: 6396
% 0.20/0.50  % (2293)Time elapsed: 0.080 s
% 0.20/0.50  % (2293)------------------------------
% 0.20/0.50  % (2293)------------------------------
% 0.20/0.50  % (2286)Success in time 0.136 s
%------------------------------------------------------------------------------
