%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 460 expanded)
%              Number of leaves         :    9 (  81 expanded)
%              Depth                    :   45
%              Number of atoms          :  545 (2768 expanded)
%              Number of equality atoms :   37 ( 273 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(subsumption_resolution,[],[f213,f35])).

fof(f35,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

fof(f213,plain,(
    ~ l3_lattices(sK0) ),
    inference(resolution,[],[f212,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f212,plain,(
    ~ l2_lattices(sK0) ),
    inference(subsumption_resolution,[],[f211,f35])).

fof(f211,plain,
    ( ~ l2_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f210,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f210,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f209,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f209,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0) ),
    inference(subsumption_resolution,[],[f208,f30])).

fof(f30,plain,(
    sK1 != k16_lattice3(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f208,plain,
    ( sK1 = k16_lattice3(sK0,sK2)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f182,f207])).

fof(f207,plain,(
    sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f206,f35])).

fof(f206,plain,
    ( sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f205,f37])).

fof(f205,plain,
    ( ~ l2_lattices(sK0)
    | sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f204,f35])).

fof(f204,plain,
    ( ~ l2_lattices(sK0)
    | sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f203,f32])).

fof(f203,plain,
    ( ~ l2_lattices(sK0)
    | sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f202,f53])).

fof(f202,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(forward_demodulation,[],[f201,f142])).

fof(f142,plain,(
    ! [X3] : k1_lattices(sK0,sK1,k16_lattice3(sK0,X3)) = k1_lattices(sK0,k16_lattice3(sK0,X3),sK1) ),
    inference(subsumption_resolution,[],[f141,f33])).

fof(f33,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f141,plain,(
    ! [X3] :
      ( k1_lattices(sK0,sK1,k16_lattice3(sK0,X3)) = k1_lattices(sK0,k16_lattice3(sK0,X3),sK1)
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f32])).

fof(f140,plain,(
    ! [X3] :
      ( k1_lattices(sK0,sK1,k16_lattice3(sK0,X3)) = k1_lattices(sK0,k16_lattice3(sK0,X3),sK1)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f35])).

fof(f139,plain,(
    ! [X3] :
      ( k1_lattices(sK0,sK1,k16_lattice3(sK0,X3)) = k1_lattices(sK0,k16_lattice3(sK0,X3),sK1)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(resolution,[],[f135,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f135,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f134,f35])).

fof(f134,plain,(
    ! [X0] :
      ( k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ v4_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f133,f37])).

fof(f133,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK0)
      | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ v4_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f132,f35])).

fof(f132,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK0)
      | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ v4_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f32])).

fof(f129,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK0)
      | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f121,f53])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | k1_lattices(sK0,sK1,X0) = k1_lattices(sK0,X0,sK1)
      | ~ v4_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f108,f32])).

fof(f108,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l2_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X0) = k1_lattices(sK0,X0,sK1)
      | ~ v4_lattices(sK0) ) ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1)
      | ~ v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_lattices)).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f201,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f200,f31])).

fof(f200,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f199,f32])).

fof(f199,plain,
    ( v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(resolution,[],[f197,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f197,plain,(
    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f196,f33])).

fof(f196,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f195,f32])).

fof(f195,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f194,f35])).

fof(f194,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f193,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f193,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f192,f33])).

fof(f192,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f191,f32])).

fof(f191,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f190,f35])).

fof(f190,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f189,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f189,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f188,f33])).

fof(f188,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f187,f32])).

fof(f187,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f186,f35])).

fof(f186,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f185,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f185,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f184,f35])).

fof(f184,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f183,f32])).

fof(f183,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f163,f53])).

fof(f163,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f162,f31])).

fof(f162,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f161,f35])).

fof(f161,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f160,f32])).

fof(f160,plain,
    ( v2_struct_0(sK0)
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(resolution,[],[f159,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f159,plain,(
    r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f158,f31])).

fof(f158,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f157,f35])).

fof(f157,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f156,f32])).

fof(f156,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f155,f33])).

fof(f155,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(resolution,[],[f101,f34])).

fof(f34,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,(
    ! [X1] :
      ( ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(sK1,u1_struct_0(X1))
      | r3_lattices(X1,k16_lattice3(X1,sK2),sK1) ) ),
    inference(resolution,[],[f28,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | r3_lattices(X0,k16_lattice3(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(f28,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f182,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f181,f31])).

fof(f181,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f180,f32])).

fof(f180,plain,
    ( v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f178,f49])).

fof(f178,plain,(
    r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f177,f33])).

fof(f177,plain,
    ( r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f176,f32])).

fof(f176,plain,
    ( r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f175,f35])).

fof(f175,plain,
    ( r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f174,f40])).

fof(f174,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f173,f33])).

fof(f173,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f172,f32])).

fof(f172,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f171,f35])).

fof(f171,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f170,f42])).

fof(f170,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f169,f33])).

fof(f169,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f168,f32])).

fof(f168,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f167,f35])).

fof(f167,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f166,f43])).

fof(f166,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f165,f35])).

fof(f165,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f164,f32])).

fof(f164,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f125,f53])).

fof(f125,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f124,f31])).

fof(f124,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f123,f35])).

fof(f123,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f122,f32])).

fof(f122,plain,
    ( v2_struct_0(sK0)
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f107,f55])).

fof(f107,plain,(
    r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f106,f31])).

fof(f106,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f105,f35])).

fof(f105,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f104,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f103,f33])).

fof(f103,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f102,f32])).

fof(f102,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f29,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

fof(f29,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:42:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.49  % (21571)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (21568)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (21578)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (21579)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (21570)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (21576)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (21580)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (21576)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f213,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    l3_lattices(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    ~l3_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f212,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    ~l2_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f211,f35])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    ~l2_lattices(sK0) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f210,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    ~l2_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f209,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f208,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    sK1 != k16_lattice3(sK0,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    sK1 = k16_lattice3(sK0,sK2) | ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))),
% 0.22/0.51    inference(backward_demodulation,[],[f182,f207])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f206,f35])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f205,f37])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ~l2_lattices(sK0) | sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f204,f35])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    ~l2_lattices(sK0) | sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f203,f32])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    ~l2_lattices(sK0) | sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f202,f53])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0) | sK1 = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f201,f142])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    ( ! [X3] : (k1_lattices(sK0,sK1,k16_lattice3(sK0,X3)) = k1_lattices(sK0,k16_lattice3(sK0,X3),sK1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f141,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    v10_lattices(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X3] : (k1_lattices(sK0,sK1,k16_lattice3(sK0,X3)) = k1_lattices(sK0,k16_lattice3(sK0,X3),sK1) | ~v10_lattices(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f140,f32])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X3] : (k1_lattices(sK0,sK1,k16_lattice3(sK0,X3)) = k1_lattices(sK0,k16_lattice3(sK0,X3),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f139,f35])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ( ! [X3] : (k1_lattices(sK0,sK1,k16_lattice3(sK0,X3)) = k1_lattices(sK0,k16_lattice3(sK0,X3),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f135,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v4_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X0] : (~v4_lattices(sK0) | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f134,f35])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X0] : (k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) | ~v4_lattices(sK0) | ~l3_lattices(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f133,f37])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X0] : (~l2_lattices(sK0) | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) | ~v4_lattices(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f132,f35])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X0] : (~l2_lattices(sK0) | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) | ~v4_lattices(sK0) | ~l3_lattices(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f129,f32])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ( ! [X0] : (~l2_lattices(sK0) | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) | ~v4_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f121,f53])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l2_lattices(sK0) | k1_lattices(sK0,sK1,X0) = k1_lattices(sK0,X0,sK1) | ~v4_lattices(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f108,f32])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X0) = k1_lattices(sK0,X0,sK1) | ~v4_lattices(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f31,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1) | ~v4_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : ((v4_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : ((v4_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,X1,X2) = k1_lattices(X0,X2,X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_lattices)).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f200,f31])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f199,f32])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(resolution,[],[f197,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f196,f33])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f195,f32])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f194,f35])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f193,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v6_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f192,f33])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f191,f32])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f190,f35])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f189,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v8_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f188,f33])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f187,f32])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f186,f35])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f185,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v9_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f184,f35])).
% 0.22/0.51  fof(f184,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f183,f32])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f163,f53])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f162,f31])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f161,f35])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f160,f32])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(resolution,[],[f159,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f158,f31])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f157,f35])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f156,f32])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f155,f33])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(resolution,[],[f101,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    v4_lattice3(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ( ! [X1] : (~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(sK1,u1_struct_0(X1)) | r3_lattices(X1,k16_lattice3(X1,sK2),sK1)) )),
% 0.22/0.51    inference(resolution,[],[f28,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_hidden(X1,X2) | r3_lattices(X0,k16_lattice3(X0,X2),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    r2_hidden(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f181,f31])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f180,f32])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(resolution,[],[f178,f49])).
% 0.22/0.51  fof(f178,plain,(
% 0.22/0.51    r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f177,f33])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f176,f32])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f175,f35])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f174,f40])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f33])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f172,f32])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f171,f35])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f170,f42])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f169,f33])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f168,f32])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f167,f35])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f166,f43])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f165,f35])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f164,f32])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f125,f53])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f124,f31])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f123,f35])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f122,f32])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(resolution,[],[f107,f55])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f106,f31])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f105,f35])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f104,f34])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f103,f33])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f102,f32])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.22/0.51    inference(resolution,[],[f29,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | r3_lattices(X0,X1,k16_lattice3(X0,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    r3_lattice3(sK0,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (21576)------------------------------
% 0.22/0.51  % (21576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21576)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (21576)Memory used [KB]: 1663
% 0.22/0.51  % (21576)Time elapsed: 0.074 s
% 0.22/0.51  % (21576)------------------------------
% 0.22/0.51  % (21576)------------------------------
% 0.22/0.51  % (21562)Success in time 0.14 s
%------------------------------------------------------------------------------
