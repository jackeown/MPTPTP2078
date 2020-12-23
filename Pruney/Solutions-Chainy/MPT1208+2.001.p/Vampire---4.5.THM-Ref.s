%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 336 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :   20
%              Number of atoms          :  367 (1533 expanded)
%              Number of equality atoms :   61 ( 205 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(subsumption_resolution,[],[f180,f32])).

fof(f32,plain,(
    sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

fof(f180,plain,(
    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(backward_demodulation,[],[f161,f179])).

fof(f179,plain,(
    sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(backward_demodulation,[],[f158,f178])).

fof(f178,plain,(
    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f177,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f177,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f176,f88])).

fof(f88,plain,(
    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f87,f33])).

fof(f87,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f58,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f58,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f38,f36])).

fof(f36,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f176,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f175,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

% (20411)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f175,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f174,f36])).

fof(f174,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f173,f67])).

fof(f67,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f66,f36])).

fof(f66,plain,
    ( ~ l3_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f65,f33])).

fof(f65,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v9_lattices(sK0) ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
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

fof(f173,plain,
    ( ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f171,f64])).

fof(f64,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f63,f36])).

fof(f63,plain,
    ( ~ l3_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f62,f33])).

fof(f62,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v8_lattices(sK0) ),
    inference(resolution,[],[f40,f34])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f171,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f166,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f166,plain,(
    r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f164,f71])).

fof(f71,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f70,f33])).

fof(f70,plain,
    ( v2_struct_0(sK0)
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f69,f35])).

fof(f35,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,
    ( ~ v14_lattices(sK0)
    | v2_struct_0(sK0)
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(subsumption_resolution,[],[f68,f58])).

fof(f68,plain,
    ( ~ l2_lattices(sK0)
    | ~ v14_lattices(sK0)
    | v2_struct_0(sK0)
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f55,f31])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | v2_struct_0(X0)
      | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0)) ) ),
    inference(subsumption_resolution,[],[f53,f44])).

fof(f53,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X2,X1) = X1
      | k6_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).

fof(f164,plain,
    ( k6_lattices(sK0) != k1_lattices(sK0,sK1,k6_lattices(sK0))
    | r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f82,f88])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X0) != X0
      | r1_lattices(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f81,f33])).

fof(f81,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X0) != X0
      | r1_lattices(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f80,f58])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X0) != X0
      | r1_lattices(sK0,sK1,X0) ) ),
    inference(resolution,[],[f49,f31])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f158,plain,(
    k4_lattices(sK0,sK1,k6_lattices(sK0)) = k2_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f86,f88])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f85,f33])).

fof(f85,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f84,f57])).

fof(f57,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f37,f36])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X0] :
      ( ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f83,f61])).

fof(f61,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f60,f36])).

fof(f60,plain,
    ( ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f59,f33])).

fof(f59,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(resolution,[],[f39,f34])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0) ) ),
    inference(resolution,[],[f51,f31])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f161,plain,(
    k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f92,f88])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f91,f33])).

fof(f91,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f90,f57])).

fof(f90,plain,(
    ! [X0] :
      ( ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f89,f61])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(resolution,[],[f52,f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:07:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (20397)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (20410)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (20397)Refutation not found, incomplete strategy% (20397)------------------------------
% 0.21/0.47  % (20397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20397)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (20397)Memory used [KB]: 10618
% 0.21/0.47  % (20397)Time elapsed: 0.061 s
% 0.21/0.47  % (20397)------------------------------
% 0.21/0.47  % (20397)------------------------------
% 0.21/0.47  % (20413)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (20405)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (20402)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (20396)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (20413)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f180,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k4_lattices(X0,k6_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.21/0.48    inference(backward_demodulation,[],[f161,f179])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.48    inference(backward_demodulation,[],[f158,f178])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f177,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f176,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f33])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    v2_struct_0(sK0) | m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.48    inference(resolution,[],[f58,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (~l2_lattices(X0) | v2_struct_0(X0) | m1_subset_1(k6_lattices(X0),u1_struct_0(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    l2_lattices(sK0)),
% 0.21/0.48    inference(resolution,[],[f38,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    l3_lattices(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f175,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % (20411)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f174,f36])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f173,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    v9_lattices(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f36])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~l3_lattices(sK0) | v9_lattices(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f33])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l3_lattices(sK0) | v9_lattices(sK0)),
% 0.21/0.48    inference(resolution,[],[f41,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v10_lattices(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f171,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v8_lattices(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f63,f36])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~l3_lattices(sK0) | v8_lattices(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f62,f33])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l3_lattices(sK0) | v8_lattices(sK0)),
% 0.21/0.48    inference(resolution,[],[f40,f34])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v8_lattices(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f166,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    r1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f164,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f33])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    v2_struct_0(sK0) | k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f69,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v14_lattices(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~v14_lattices(sK0) | v2_struct_0(sK0) | k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f58])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~l2_lattices(sK0) | ~v14_lattices(sK0) | v2_struct_0(sK0) | k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.48    inference(resolution,[],[f55,f31])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v14_lattices(X0) | v2_struct_0(X0) | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f53,f44])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~v14_lattices(X0) | ~m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k6_lattices(X0) = k1_lattices(X0,X2,k6_lattices(X0))) )),
% 0.21/0.48    inference(equality_resolution,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~v14_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X2,X1) = X1 | k6_lattices(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : ((! [X1] : ((k6_lattices(X0) = X1 <=> ! [X2] : ((k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v14_lattices(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k6_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k1_lattices(X0,X2,X1) = X1 & k1_lattices(X0,X1,X2) = X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    k6_lattices(sK0) != k1_lattices(sK0,sK1,k6_lattices(sK0)) | r1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.48    inference(resolution,[],[f82,f88])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X0) != X0 | r1_lattices(sK0,sK1,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f33])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X0) != X0 | r1_lattices(sK0,sK1,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f58])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0] : (~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X0) != X0 | r1_lattices(sK0,sK1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f49,f31])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    k4_lattices(sK0,sK1,k6_lattices(sK0)) = k2_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.48    inference(resolution,[],[f86,f88])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f33])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    l1_lattices(sK0)),
% 0.21/0.48    inference(resolution,[],[f37,f36])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    v6_lattices(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f60,f36])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f59,f33])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.21/0.48    inference(resolution,[],[f39,f34])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v6_lattices(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k2_lattices(sK0,sK1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f51,f31])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.48    inference(resolution,[],[f92,f88])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f33])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f90,f57])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f89,f61])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1)) )),
% 0.21/0.48    inference(resolution,[],[f52,f31])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (20413)------------------------------
% 0.21/0.48  % (20413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20413)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (20413)Memory used [KB]: 1663
% 0.21/0.48  % (20413)Time elapsed: 0.068 s
% 0.21/0.48  % (20413)------------------------------
% 0.21/0.48  % (20413)------------------------------
% 0.21/0.49  % (20395)Success in time 0.125 s
%------------------------------------------------------------------------------
