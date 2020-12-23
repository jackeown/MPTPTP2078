%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 612 expanded)
%              Number of leaves         :   10 ( 108 expanded)
%              Depth                    :   45
%              Number of atoms          :  676 (3637 expanded)
%              Number of equality atoms :   69 ( 381 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f398,plain,(
    $false ),
    inference(subsumption_resolution,[],[f397,f38])).

fof(f38,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

fof(f397,plain,(
    ~ l3_lattices(sK0) ),
    inference(resolution,[],[f396,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f396,plain,(
    ~ l2_lattices(sK0) ),
    inference(subsumption_resolution,[],[f395,f38])).

fof(f395,plain,
    ( ~ l2_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f391,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f391,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f390,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f390,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0) ),
    inference(subsumption_resolution,[],[f389,f33])).

fof(f33,plain,(
    sK1 != k16_lattice3(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f389,plain,
    ( sK1 = k16_lattice3(sK0,sK2)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f345,f388])).

fof(f388,plain,(
    sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f387,f38])).

fof(f387,plain,
    ( sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f386,f40])).

fof(f386,plain,
    ( ~ l2_lattices(sK0)
    | sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f385,f38])).

fof(f385,plain,
    ( ~ l2_lattices(sK0)
    | sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f381,f35])).

fof(f381,plain,
    ( ~ l2_lattices(sK0)
    | sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f380,f56])).

fof(f380,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(forward_demodulation,[],[f379,f278])).

fof(f278,plain,(
    ! [X0] : k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) ),
    inference(backward_demodulation,[],[f256,f277])).

fof(f277,plain,(
    ! [X0] : k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) ),
    inference(subsumption_resolution,[],[f276,f36])).

fof(f36,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f276,plain,(
    ! [X0] :
      ( k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f275,f35])).

fof(f275,plain,(
    ! [X0] :
      ( k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f274,f38])).

fof(f274,plain,(
    ! [X0] :
      ( k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(resolution,[],[f273,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v4_lattices(X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f273,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f272,f38])).

fof(f272,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f238,f40])).

fof(f238,plain,(
    ! [X2] :
      ( ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k3_lattices(sK0,k16_lattice3(sK0,X2),sK1) ) ),
    inference(subsumption_resolution,[],[f237,f38])).

fof(f237,plain,(
    ! [X2] :
      ( ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k3_lattices(sK0,k16_lattice3(sK0,X2),sK1)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f236,f35])).

fof(f236,plain,(
    ! [X2] :
      ( ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k3_lattices(sK0,k16_lattice3(sK0,X2),sK1)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f164,f56])).

fof(f164,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,sK1,X10) = k3_lattices(sK0,X10,sK1) ) ),
    inference(subsumption_resolution,[],[f159,f35])).

fof(f159,plain,(
    ! [X10] :
      ( v2_struct_0(sK0)
      | ~ v4_lattices(sK0)
      | ~ l2_lattices(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | k3_lattices(sK0,sK1,X10) = k3_lattices(sK0,X10,sK1) ) ),
    inference(resolution,[],[f34,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
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

% (27902)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f34,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f256,plain,(
    ! [X0] : k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) ),
    inference(subsumption_resolution,[],[f255,f36])).

fof(f255,plain,(
    ! [X0] :
      ( k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f254,f35])).

fof(f254,plain,(
    ! [X0] :
      ( k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f253,f38])).

fof(f253,plain,(
    ! [X0] :
      ( k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(resolution,[],[f252,f41])).

fof(f252,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f251,f38])).

fof(f251,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f232,f40])).

fof(f232,plain,(
    ! [X2] :
      ( ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,k16_lattice3(sK0,X2),sK1) = k1_lattices(sK0,k16_lattice3(sK0,X2),sK1) ) ),
    inference(subsumption_resolution,[],[f231,f38])).

fof(f231,plain,(
    ! [X2] :
      ( ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,k16_lattice3(sK0,X2),sK1) = k1_lattices(sK0,k16_lattice3(sK0,X2),sK1)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f230,f35])).

fof(f230,plain,(
    ! [X2] :
      ( ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,k16_lattice3(sK0,X2),sK1) = k1_lattices(sK0,k16_lattice3(sK0,X2),sK1)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f163,f56])).

fof(f163,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,X9,sK1) = k1_lattices(sK0,X9,sK1) ) ),
    inference(subsumption_resolution,[],[f158,f35])).

fof(f158,plain,(
    ! [X9] :
      ( v2_struct_0(sK0)
      | ~ v4_lattices(sK0)
      | ~ l2_lattices(sK0)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | k3_lattices(sK0,X9,sK1) = k1_lattices(sK0,X9,sK1) ) ),
    inference(resolution,[],[f34,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f379,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f378,f34])).

fof(f378,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f374,f35])).

fof(f374,plain,
    ( v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(resolution,[],[f372,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

% (27911)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f372,plain,(
    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f371,f36])).

fof(f371,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f370,f35])).

fof(f370,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f369,f38])).

fof(f369,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f368,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f368,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f367,f36])).

fof(f367,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f366,f35])).

fof(f366,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f365,f38])).

fof(f365,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f362,f45])).

% (27901)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f45,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f362,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f361,f36])).

fof(f361,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f360,f35])).

fof(f360,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f359,f38])).

fof(f359,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f358,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f358,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f357,f38])).

fof(f357,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f353,f35])).

fof(f353,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f307,f56])).

fof(f307,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f306,f34])).

fof(f306,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f305,f38])).

fof(f305,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f301,f35])).

fof(f301,plain,
    ( v2_struct_0(sK0)
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(resolution,[],[f300,f58])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f300,plain,(
    r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f299,f34])).

fof(f299,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f298,f38])).

fof(f298,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f297,f35])).

fof(f297,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f296,f36])).

fof(f296,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(resolution,[],[f122,f37])).

fof(f37,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f122,plain,(
    ! [X1] :
      ( ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(sK1,u1_struct_0(X1))
      | r3_lattices(X1,k16_lattice3(X1,sK2),sK1) ) ),
    inference(resolution,[],[f31,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | r3_lattices(X0,k16_lattice3(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

fof(f31,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f345,plain,
    ( k16_lattice3(sK0,sK2) = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f344,f244])).

fof(f244,plain,(
    ! [X0] : k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) ),
    inference(subsumption_resolution,[],[f243,f36])).

fof(f243,plain,(
    ! [X0] :
      ( k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0))
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f242,f35])).

fof(f242,plain,(
    ! [X0] :
      ( k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f241,f38])).

fof(f241,plain,(
    ! [X0] :
      ( k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0) ) ),
    inference(resolution,[],[f240,f41])).

fof(f240,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f239,f38])).

% (27908)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f239,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0))
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f217,f40])).

fof(f217,plain,(
    ! [X2] :
      ( ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k1_lattices(sK0,sK1,k16_lattice3(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f216,f38])).

fof(f216,plain,(
    ! [X2] :
      ( ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k1_lattices(sK0,sK1,k16_lattice3(sK0,X2))
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f215,f35])).

fof(f215,plain,(
    ! [X2] :
      ( ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k1_lattices(sK0,sK1,k16_lattice3(sK0,X2))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f162,f56])).

fof(f162,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8) ) ),
    inference(subsumption_resolution,[],[f157,f35])).

fof(f157,plain,(
    ! [X8] :
      ( v2_struct_0(sK0)
      | ~ v4_lattices(sK0)
      | ~ l2_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8) ) ),
    inference(resolution,[],[f34,f59])).

fof(f344,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f343,f34])).

fof(f343,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f339,f35])).

fof(f339,plain,
    ( v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f337,f55])).

fof(f337,plain,(
    r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f336,f36])).

fof(f336,plain,
    ( r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f335,f35])).

fof(f335,plain,
    ( r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f334,f38])).

fof(f334,plain,
    ( r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f331,f43])).

fof(f331,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f330,f36])).

fof(f330,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f329,f35])).

fof(f329,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f328,f38])).

fof(f328,plain,
    ( ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f327,f45])).

fof(f327,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f326,f36])).

fof(f326,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f325,f35])).

fof(f325,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f324,f38])).

fof(f324,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f323,f46])).

fof(f323,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f322,f38])).

fof(f322,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f318,f35])).

fof(f318,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f206,f56])).

fof(f206,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f205,f34])).

fof(f205,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f204,f38])).

fof(f204,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f200,f35])).

fof(f200,plain,
    ( v2_struct_0(sK0)
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f199,f58])).

fof(f199,plain,(
    r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f198,f38])).

fof(f198,plain,
    ( r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f194,f35])).

fof(f194,plain,
    ( r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f143,f56])).

fof(f143,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f142,f34])).

fof(f142,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f141,f38])).

fof(f141,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f140,f37])).

fof(f140,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f139,f36])).

fof(f139,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f126,f35])).

fof(f126,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f32,f62])).

fof(f62,plain,(
    ! [X2,X0,X3] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,k16_lattice3(X0,X2)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,X1)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
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
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f32,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:57:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (27904)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (27913)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (27914)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (27913)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f398,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f397,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    l3_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).
% 0.21/0.49  fof(f397,plain,(
% 0.21/0.49    ~l3_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f396,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.49  fof(f396,plain,(
% 0.21/0.49    ~l2_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f395,f38])).
% 0.21/0.49  fof(f395,plain,(
% 0.21/0.49    ~l2_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f391,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    ~l2_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f390,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 0.21/0.49  fof(f390,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f389,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    sK1 != k16_lattice3(sK0,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f389,plain,(
% 0.21/0.49    sK1 = k16_lattice3(sK0,sK2) | ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f345,f388])).
% 0.21/0.49  fof(f388,plain,(
% 0.21/0.49    sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f387,f38])).
% 0.21/0.49  fof(f387,plain,(
% 0.21/0.49    sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f386,f40])).
% 0.21/0.49  fof(f386,plain,(
% 0.21/0.49    ~l2_lattices(sK0) | sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f385,f38])).
% 0.21/0.49  fof(f385,plain,(
% 0.21/0.49    ~l2_lattices(sK0) | sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f381,f35])).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    ~l2_lattices(sK0) | sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f380,f56])).
% 0.21/0.49  fof(f380,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l2_lattices(sK0) | sK1 = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(forward_demodulation,[],[f379,f278])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    ( ! [X0] : (k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k1_lattices(sK0,k16_lattice3(sK0,X0),sK1)) )),
% 0.21/0.49    inference(backward_demodulation,[],[f256,f277])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    ( ! [X0] : (k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f276,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    v10_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    ( ! [X0] : (k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) | ~v10_lattices(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f275,f35])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ( ! [X0] : (k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f274,f38])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    ( ! [X0] : (k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f273,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v4_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_lattices(sK0) | k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f272,f38])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_lattices(sK0) | k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) | ~l3_lattices(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f238,f40])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    ( ! [X2] : (~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k3_lattices(sK0,k16_lattice3(sK0,X2),sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f237,f38])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ( ! [X2] : (~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k3_lattices(sK0,k16_lattice3(sK0,X2),sK1) | ~l3_lattices(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f236,f35])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ( ! [X2] : (~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k3_lattices(sK0,k16_lattice3(sK0,X2),sK1) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f164,f56])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ( ! [X10] : (~m1_subset_1(X10,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,sK1,X10) = k3_lattices(sK0,X10,sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f159,f35])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ( ! [X10] : (v2_struct_0(sK0) | ~v4_lattices(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k3_lattices(sK0,sK1,X10) = k3_lattices(sK0,X10,sK1)) )),
% 0.21/0.49    inference(resolution,[],[f34,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v4_lattices(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  % (27902)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ( ! [X0] : (k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f255,f36])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ( ! [X0] : (k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) | ~v10_lattices(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f254,f35])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ( ! [X0] : (k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f253,f38])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    ( ! [X0] : (k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f252,f41])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_lattices(sK0) | k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f251,f38])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_lattices(sK0) | k1_lattices(sK0,k16_lattice3(sK0,X0),sK1) = k3_lattices(sK0,k16_lattice3(sK0,X0),sK1) | ~l3_lattices(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f232,f40])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X2] : (~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,k16_lattice3(sK0,X2),sK1) = k1_lattices(sK0,k16_lattice3(sK0,X2),sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f231,f38])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ( ! [X2] : (~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,k16_lattice3(sK0,X2),sK1) = k1_lattices(sK0,k16_lattice3(sK0,X2),sK1) | ~l3_lattices(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f230,f35])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ( ! [X2] : (~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,k16_lattice3(sK0,X2),sK1) = k1_lattices(sK0,k16_lattice3(sK0,X2),sK1) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f163,f56])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ( ! [X9] : (~m1_subset_1(X9,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,X9,sK1) = k1_lattices(sK0,X9,sK1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f158,f35])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ( ! [X9] : (v2_struct_0(sK0) | ~v4_lattices(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | k3_lattices(sK0,X9,sK1) = k1_lattices(sK0,X9,sK1)) )),
% 0.21/0.49    inference(resolution,[],[f34,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v4_lattices(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.21/0.49  fof(f379,plain,(
% 0.21/0.49    ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f378,f34])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f374,f35])).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(resolution,[],[f372,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 0.21/0.49  % (27911)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f371,f36])).
% 0.21/0.49  fof(f371,plain,(
% 0.21/0.49    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f370,f35])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f369,f38])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f368,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v6_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f367,f36])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f366,f35])).
% 0.21/0.49  fof(f366,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f365,f38])).
% 0.21/0.49  fof(f365,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f362,f45])).
% 0.21/0.49  % (27901)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v8_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f362,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f361,f36])).
% 0.21/0.49  fof(f361,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f360,f35])).
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f359,f38])).
% 0.21/0.49  fof(f359,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f358,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v9_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f358,plain,(
% 0.21/0.49    ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f357,f38])).
% 0.21/0.49  fof(f357,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f353,f35])).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f307,f56])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f306,f34])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f305,f38])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f301,f35])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(resolution,[],[f300,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f299,f34])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f298,f38])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f297,f35])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f296,f36])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.21/0.49    inference(resolution,[],[f122,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v4_lattice3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X1] : (~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(sK1,u1_struct_0(X1)) | r3_lattices(X1,k16_lattice3(X1,sK2),sK1)) )),
% 0.21/0.49    inference(resolution,[],[f31,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_hidden(X1,X2) | r3_lattices(X0,k16_lattice3(X0,X2),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    r2_hidden(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f345,plain,(
% 0.21/0.49    k16_lattice3(sK0,sK2) = k3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.49    inference(forward_demodulation,[],[f344,f244])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    ( ! [X0] : (k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f243,f36])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ( ! [X0] : (k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) | ~v10_lattices(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f242,f35])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    ( ! [X0] : (k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) | v2_struct_0(sK0) | ~v10_lattices(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f241,f38])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ( ! [X0] : (k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f240,f41])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_lattices(sK0) | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f239,f38])).
% 0.21/0.49  % (27908)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_lattices(sK0) | k1_lattices(sK0,sK1,k16_lattice3(sK0,X0)) = k3_lattices(sK0,sK1,k16_lattice3(sK0,X0)) | ~l3_lattices(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f217,f40])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    ( ! [X2] : (~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k1_lattices(sK0,sK1,k16_lattice3(sK0,X2))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f216,f38])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ( ! [X2] : (~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k1_lattices(sK0,sK1,k16_lattice3(sK0,X2)) | ~l3_lattices(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f215,f35])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ( ! [X2] : (~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,sK1,k16_lattice3(sK0,X2)) = k1_lattices(sK0,sK1,k16_lattice3(sK0,X2)) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f162,f56])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f157,f35])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X8] : (v2_struct_0(sK0) | ~v4_lattices(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | k3_lattices(sK0,sK1,X8) = k1_lattices(sK0,sK1,X8)) )),
% 0.21/0.49    inference(resolution,[],[f34,f59])).
% 0.21/0.49  fof(f344,plain,(
% 0.21/0.49    ~l2_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f343,f34])).
% 0.21/0.49  fof(f343,plain,(
% 0.21/0.49    ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f339,f35])).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | k16_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(resolution,[],[f337,f55])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f336,f36])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f335,f35])).
% 0.21/0.49  fof(f335,plain,(
% 0.21/0.49    r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f334,f38])).
% 0.21/0.49  fof(f334,plain,(
% 0.21/0.49    r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f331,f43])).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f330,f36])).
% 0.21/0.49  fof(f330,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f329,f35])).
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f328,f38])).
% 0.21/0.49  fof(f328,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f327,f45])).
% 0.21/0.49  fof(f327,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f326,f36])).
% 0.21/0.49  fof(f326,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f325,f35])).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f324,f38])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f323,f46])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f322,f38])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f318,f35])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.49    inference(resolution,[],[f206,f56])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f205,f34])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f204,f38])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f200,f35])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(resolution,[],[f199,f58])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f198,f38])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | ~l3_lattices(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f194,f35])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.21/0.50    inference(resolution,[],[f143,f56])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f142,f34])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f141,f38])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f140,f37])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f139,f36])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f126,f35])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.50    inference(resolution,[],[f32,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,k16_lattice3(X0,X2))) )),
% 0.21/0.50    inference(equality_resolution,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,X1) | k16_lattice3(X0,X2) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    r3_lattice3(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (27913)------------------------------
% 0.21/0.50  % (27913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27913)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (27913)Memory used [KB]: 1663
% 0.21/0.50  % (27913)Time elapsed: 0.080 s
% 0.21/0.50  % (27913)------------------------------
% 0.21/0.50  % (27913)------------------------------
% 0.21/0.50  % (27909)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (27917)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (27901)Refutation not found, incomplete strategy% (27901)------------------------------
% 0.21/0.50  % (27901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27901)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (27901)Memory used [KB]: 10618
% 0.21/0.50  % (27901)Time elapsed: 0.067 s
% 0.21/0.50  % (27901)------------------------------
% 0.21/0.50  % (27901)------------------------------
% 0.21/0.50  % (27898)Success in time 0.135 s
%------------------------------------------------------------------------------
