%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1203+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:11 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  103 (1634 expanded)
%              Number of leaves         :   18 ( 736 expanded)
%              Depth                    :   17
%              Number of atoms          :  443 (15058 expanded)
%              Number of equality atoms :  121 (5429 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3972,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3971,f2282])).

fof(f2282,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f2181])).

fof(f2181,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2055,f2180,f2179,f2178,f2177])).

fof(f2177,plain,
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

fof(f2178,plain,
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

fof(f2179,plain,
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

fof(f2180,plain,
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

fof(f2055,plain,(
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
    inference(flattening,[],[f2054])).

fof(f2054,plain,(
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
    inference(ennf_transformation,[],[f2052])).

fof(f2052,negated_conjecture,(
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
    inference(negated_conjecture,[],[f2051])).

fof(f2051,conjecture,(
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

fof(f3971,plain,(
    sK2 = sK3 ),
    inference(backward_demodulation,[],[f3955,f3970])).

fof(f3970,plain,(
    sK2 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f3891,f2855])).

fof(f2855,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f2714,f2730])).

fof(f2730,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f2273,f2451,f2277,f2278,f2453,f2283])).

fof(f2283,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2057])).

fof(f2057,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2056])).

fof(f2056,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2011])).

fof(f2011,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f2453,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f2273,f2274,f2276,f2338])).

fof(f2338,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2106])).

fof(f2106,plain,(
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
    inference(flattening,[],[f2105])).

fof(f2105,plain,(
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
    inference(ennf_transformation,[],[f2009])).

fof(f2009,axiom,(
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

fof(f2276,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2181])).

fof(f2274,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f2181])).

fof(f2278,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2181])).

fof(f2277,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2181])).

fof(f2451,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f2276,f2331])).

fof(f2331,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2102])).

fof(f2102,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2029])).

fof(f2029,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f2273,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2181])).

fof(f2714,plain,(
    k3_lattices(sK0,sK2,sK1) = k1_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f2273,f2451,f2277,f2278,f2453,f2284])).

fof(f2284,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2059])).

fof(f2059,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2058])).

fof(f2058,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2035])).

fof(f2035,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f3891,plain,(
    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f2273,f2276,f2277,f2278,f2458,f2357])).

fof(f2357,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2232])).

fof(f2232,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK26(X0) != k2_lattices(X0,sK26(X0),k1_lattices(X0,sK26(X0),sK27(X0)))
            & m1_subset_1(sK27(X0),u1_struct_0(X0))
            & m1_subset_1(sK26(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26,sK27])],[f2229,f2231,f2230])).

fof(f2230,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK26(X0) != k2_lattices(X0,sK26(X0),k1_lattices(X0,sK26(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK26(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2231,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK26(X0) != k2_lattices(X0,sK26(X0),k1_lattices(X0,sK26(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK26(X0) != k2_lattices(X0,sK26(X0),k1_lattices(X0,sK26(X0),sK27(X0)))
        & m1_subset_1(sK27(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2229,plain,(
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
    inference(rectify,[],[f2228])).

fof(f2228,plain,(
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
    inference(nnf_transformation,[],[f2121])).

fof(f2121,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2120])).

fof(f2120,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2020])).

fof(f2020,axiom,(
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

fof(f2458,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f2273,f2274,f2276,f2343])).

fof(f2343,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2106])).

fof(f3955,plain,(
    sK3 = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f3580,f3954])).

fof(f3954,plain,(
    sK3 = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f3895,f2834])).

fof(f2834,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f2718,f2774])).

fof(f2774,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f2734,f2281])).

fof(f2281,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f2181])).

fof(f2734,plain,(
    k3_lattices(sK0,sK1,sK3) = k3_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f2273,f2451,f2277,f2279,f2453,f2283])).

fof(f2279,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2181])).

fof(f2718,plain,(
    k3_lattices(sK0,sK3,sK1) = k1_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f2273,f2451,f2277,f2279,f2453,f2284])).

fof(f3895,plain,(
    sK3 = k2_lattices(sK0,sK3,k1_lattices(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f2273,f2276,f2277,f2279,f2458,f2357])).

fof(f3580,plain,(
    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f3562,f3574])).

fof(f3574,plain,(
    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f3452,f3315])).

fof(f3315,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f2273,f2450,f2277,f2278,f2455,f2299])).

fof(f2299,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2069])).

fof(f2069,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2068])).

fof(f2068,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2012])).

fof(f2012,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f2455,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f2273,f2274,f2276,f2340])).

fof(f2340,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2106])).

fof(f2450,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f2276,f2330])).

fof(f2330,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2102])).

fof(f3452,plain,(
    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f3435,f3331])).

fof(f3331,plain,(
    k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f2273,f2450,f2277,f2278,f2455,f2300])).

fof(f2300,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2071])).

fof(f2071,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2070])).

fof(f2070,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2037])).

fof(f2037,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f3435,plain,(
    k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k2_lattices(sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f2836,f3333])).

fof(f3333,plain,(
    k4_lattices(sK0,sK2,sK3) = k2_lattices(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f2273,f2450,f2279,f2278,f2455,f2300])).

fof(f2836,plain,(
    k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k2_lattices(sK0,sK2,sK1)) = k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f2627,f2834])).

fof(f2627,plain,(
    k2_lattices(sK0,sK2,k1_lattices(sK0,sK3,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,sK3),k2_lattices(sK0,sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f2273,f2276,f2275,f2278,f2277,f2279,f2332])).

fof(f2332,plain,(
    ! [X6,X4,X0,X5] :
      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2219])).

fof(f2219,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k2_lattices(X0,sK20(X0),k1_lattices(X0,sK21(X0),sK22(X0))) != k1_lattices(X0,k2_lattices(X0,sK20(X0),sK21(X0)),k2_lattices(X0,sK20(X0),sK22(X0)))
            & m1_subset_1(sK22(X0),u1_struct_0(X0))
            & m1_subset_1(sK21(X0),u1_struct_0(X0))
            & m1_subset_1(sK20(X0),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20,sK21,sK22])],[f2215,f2218,f2217,f2216])).

fof(f2216,plain,(
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
                ( k2_lattices(X0,sK20(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK20(X0),X2),k2_lattices(X0,sK20(X0),X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK20(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2217,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK20(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK20(X0),X2),k2_lattices(X0,sK20(X0),X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK20(X0),k1_lattices(X0,sK21(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK20(X0),sK21(X0)),k2_lattices(X0,sK20(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK21(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2218,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK20(X0),k1_lattices(X0,sK21(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK20(X0),sK21(X0)),k2_lattices(X0,sK20(X0),X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK20(X0),k1_lattices(X0,sK21(X0),sK22(X0))) != k1_lattices(X0,k2_lattices(X0,sK20(X0),sK21(X0)),k2_lattices(X0,sK20(X0),sK22(X0)))
        & m1_subset_1(sK22(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2215,plain,(
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
    inference(rectify,[],[f2214])).

fof(f2214,plain,(
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
    inference(nnf_transformation,[],[f2104])).

fof(f2104,plain,(
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
    inference(flattening,[],[f2103])).

fof(f2103,plain,(
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
    inference(ennf_transformation,[],[f2013])).

fof(f2013,axiom,(
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

fof(f2275,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f2181])).

fof(f3562,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f3546,f3549])).

fof(f3549,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1) ),
    inference(forward_demodulation,[],[f3319,f2280])).

fof(f2280,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f2181])).

fof(f3319,plain,(
    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f2273,f2450,f2277,f2279,f2455,f2299])).

fof(f3546,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK2,sK3),k4_lattices(sK0,sK3,sK1)) ),
    inference(backward_demodulation,[],[f3422,f3320])).

fof(f3320,plain,(
    k4_lattices(sK0,sK2,sK3) = k4_lattices(sK0,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f2273,f2450,f2278,f2279,f2455,f2299])).

fof(f3422,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK3,sK2),k4_lattices(sK0,sK3,sK1)) ),
    inference(backward_demodulation,[],[f3410,f3335])).

fof(f3335,plain,(
    k4_lattices(sK0,sK3,sK1) = k2_lattices(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f2273,f2450,f2277,f2279,f2455,f2300])).

fof(f3410,plain,(
    k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) ),
    inference(backward_demodulation,[],[f2856,f3336])).

fof(f3336,plain,(
    k4_lattices(sK0,sK3,sK2) = k2_lattices(sK0,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f2273,f2450,f2278,f2279,f2455,f2300])).

fof(f2856,plain,(
    k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) = k2_lattices(sK0,sK3,k3_lattices(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f2614,f2855])).

fof(f2614,plain,(
    k2_lattices(sK0,sK3,k1_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK3,sK2),k2_lattices(sK0,sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f2273,f2276,f2275,f2277,f2278,f2279,f2332])).
%------------------------------------------------------------------------------
