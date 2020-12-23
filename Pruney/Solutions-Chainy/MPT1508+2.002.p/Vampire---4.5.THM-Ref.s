%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 308 expanded)
%              Number of leaves         :    5 (  53 expanded)
%              Depth                    :   34
%              Number of atoms          :  369 (1967 expanded)
%              Number of equality atoms :   29 ( 220 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f297,plain,(
    $false ),
    inference(subsumption_resolution,[],[f296,f22])).

fof(f22,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

% (13802)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f296,plain,(
    ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f295,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f295,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f294,f24])).

fof(f24,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f294,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f288,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f288,plain,(
    ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f287,f22])).

fof(f287,plain,
    ( ~ v6_lattices(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f286,f21])).

fof(f286,plain,
    ( ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f285,f24])).

fof(f285,plain,
    ( ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f284,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f284,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f283,f22])).

fof(f283,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f282,f21])).

fof(f282,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f281,f24])).

fof(f281,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f280,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f280,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f279,f217])).

fof(f217,plain,(
    ~ r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f216,f19])).

fof(f19,plain,(
    sK1 != k16_lattice3(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f216,plain,
    ( ~ r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | sK1 = k16_lattice3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f206,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f206,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | sK1 = k16_lattice3(sK0,sK2) ),
    inference(resolution,[],[f85,f18])).

fof(f18,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f85,plain,(
    ! [X4,X5] :
      ( ~ r3_lattice3(sK0,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,sK3(sK0,X4,X5),X4)
      | k16_lattice3(sK0,X5) = X4 ) ),
    inference(subsumption_resolution,[],[f84,f24])).

fof(f84,plain,(
    ! [X4,X5] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X4,X5)
      | ~ r3_lattices(sK0,sK3(sK0,X4,X5),X4)
      | k16_lattice3(sK0,X5) = X4 ) ),
    inference(subsumption_resolution,[],[f83,f22])).

fof(f83,plain,(
    ! [X4,X5] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X4,X5)
      | ~ r3_lattices(sK0,sK3(sK0,X4,X5),X4)
      | k16_lattice3(sK0,X5) = X4 ) ),
    inference(subsumption_resolution,[],[f74,f21])).

fof(f74,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X4,X5)
      | ~ r3_lattices(sK0,sK3(sK0,X4,X5),X4)
      | k16_lattice3(sK0,X5) = X4 ) ),
    inference(resolution,[],[f23,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ r3_lattices(X0,sK3(X0,X1,X2),X1)
      | k16_lattice3(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f23,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f279,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f278,f20])).

fof(f278,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f277,f143])).

fof(f143,plain,(
    m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f142,f19])).

fof(f142,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 = k16_lattice3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f134,f20])).

fof(f134,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | sK1 = k16_lattice3(sK0,sK2) ),
    inference(resolution,[],[f79,f18])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | k16_lattice3(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f78,f24])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X0,X1)
      | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | k16_lattice3(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f77,f22])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X0,X1)
      | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | k16_lattice3(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f72,f21])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X0,X1)
      | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
      | k16_lattice3(sK0,X1) = X0 ) ),
    inference(resolution,[],[f23,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k16_lattice3(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f277,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f276,f24])).

fof(f276,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f275,f21])).

fof(f275,plain,
    ( v2_struct_0(sK0)
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) ),
    inference(resolution,[],[f265,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f265,plain,(
    r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f264,f21])).

fof(f264,plain,
    ( r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f263,f20])).

fof(f263,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f262,f143])).

fof(f262,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f24])).

fof(f254,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f109,f170])).

fof(f170,plain,(
    r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f169,f19])).

fof(f169,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2)
    | sK1 = k16_lattice3(sK0,sK2) ),
    inference(subsumption_resolution,[],[f161,f20])).

fof(f161,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2)
    | sK1 = k16_lattice3(sK0,sK2) ),
    inference(resolution,[],[f82,f18])).

fof(f82,plain,(
    ! [X2,X3] :
      ( ~ r3_lattice3(sK0,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r3_lattice3(sK0,sK3(sK0,X2,X3),X3)
      | k16_lattice3(sK0,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f81,f24])).

fof(f81,plain,(
    ! [X2,X3] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X2,X3)
      | r3_lattice3(sK0,sK3(sK0,X2,X3),X3)
      | k16_lattice3(sK0,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f80,plain,(
    ! [X2,X3] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X2,X3)
      | r3_lattice3(sK0,sK3(sK0,X2,X3),X3)
      | k16_lattice3(sK0,X3) = X2 ) ),
    inference(subsumption_resolution,[],[f73,f21])).

fof(f73,plain,(
    ! [X2,X3] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r3_lattice3(sK0,X2,X3)
      | r3_lattice3(sK0,sK3(sK0,X2,X3),X3)
      | k16_lattice3(sK0,X3) = X2 ) ),
    inference(resolution,[],[f23,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | r3_lattice3(X0,sK3(X0,X1,X2),X2)
      | k16_lattice3(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(X0,X1,sK2)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK1,u1_struct_0(X0))
      | r1_lattices(X0,X1,sK1)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f17,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X1,X3)
      | ~ r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(f17,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (13801)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (13800)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (13811)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (13809)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (13809)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f297,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f296,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    v10_lattices(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f7])).
% 0.20/0.48  % (13802)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).
% 0.20/0.48  fof(f296,plain,(
% 0.20/0.48    ~v10_lattices(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f295,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f295,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f294,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    l3_lattices(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f294,plain,(
% 0.20/0.48    ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.20/0.48    inference(resolution,[],[f288,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v6_lattices(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.48  fof(f288,plain,(
% 0.20/0.48    ~v6_lattices(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f287,f22])).
% 0.20/0.48  fof(f287,plain,(
% 0.20/0.48    ~v6_lattices(sK0) | ~v10_lattices(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f286,f21])).
% 0.20/0.48  fof(f286,plain,(
% 0.20/0.48    ~v6_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f285,f24])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    ~v6_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.20/0.48    inference(resolution,[],[f284,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v8_lattices(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f284,plain,(
% 0.20/0.48    ~v8_lattices(sK0) | ~v6_lattices(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f283,f22])).
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~v10_lattices(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f282,f21])).
% 0.20/0.48  fof(f282,plain,(
% 0.20/0.48    ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f281,f24])).
% 0.20/0.48  fof(f281,plain,(
% 0.20/0.48    ~v8_lattices(sK0) | ~v6_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.20/0.48    inference(resolution,[],[f280,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v9_lattices(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f280,plain,(
% 0.20/0.48    ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f279,f217])).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    ~r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f216,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    sK1 != k16_lattice3(sK0,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    ~r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | sK1 = k16_lattice3(sK0,sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f206,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f206,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | sK1 = k16_lattice3(sK0,sK2)),
% 0.20/0.48    inference(resolution,[],[f85,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    r3_lattice3(sK0,sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ( ! [X4,X5] : (~r3_lattice3(sK0,X4,X5) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,X4,X5),X4) | k16_lattice3(sK0,X5) = X4) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f84,f24])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X4,X5] : (~l3_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X4,X5) | ~r3_lattices(sK0,sK3(sK0,X4,X5),X4) | k16_lattice3(sK0,X5) = X4) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f83,f22])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ( ! [X4,X5] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X4,X5) | ~r3_lattices(sK0,sK3(sK0,X4,X5),X4) | k16_lattice3(sK0,X5) = X4) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f74,f21])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ( ! [X4,X5] : (v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X4,X5) | ~r3_lattices(sK0,sK3(sK0,X4,X5),X4) | k16_lattice3(sK0,X5) = X4) )),
% 0.20/0.48    inference(resolution,[],[f23,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~r3_lattices(X0,sK3(X0,X1,X2),X1) | k16_lattice3(X0,X2) = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    v4_lattice3(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f279,plain,(
% 0.20/0.48    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f278,f20])).
% 0.20/0.48  fof(f278,plain,(
% 0.20/0.48    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f277,f143])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f142,f19])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | sK1 = k16_lattice3(sK0,sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f134,f20])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | sK1 = k16_lattice3(sK0,sK2)),
% 0.20/0.48    inference(resolution,[],[f79,f18])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r3_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f78,f24])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f77,f22])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f72,f21])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,X1) | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0)) | k16_lattice3(sK0,X1) = X0) )),
% 0.20/0.48    inference(resolution,[],[f23,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | k16_lattice3(X0,X2) = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f277,plain,(
% 0.20/0.48    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f276,f24])).
% 0.20/0.48  fof(f276,plain,(
% 0.20/0.48    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f275,f21])).
% 0.20/0.48  fof(f275,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,sK3(sK0,sK1,sK2),sK1)),
% 0.20/0.48    inference(resolution,[],[f265,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f264,f21])).
% 0.20/0.48  fof(f264,plain,(
% 0.20/0.48    r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f263,f20])).
% 0.20/0.48  fof(f263,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f262,f143])).
% 0.20/0.48  fof(f262,plain,(
% 0.20/0.48    ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f254,f24])).
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,sK1,sK2),sK1) | v2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f109,f170])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f169,f19])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2) | sK1 = k16_lattice3(sK0,sK2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f161,f20])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattice3(sK0,sK3(sK0,sK1,sK2),sK2) | sK1 = k16_lattice3(sK0,sK2)),
% 0.20/0.48    inference(resolution,[],[f82,f18])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~r3_lattice3(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_lattice3(sK0,sK3(sK0,X2,X3),X3) | k16_lattice3(sK0,X3) = X2) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f81,f24])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X3) | r3_lattice3(sK0,sK3(sK0,X2,X3),X3) | k16_lattice3(sK0,X3) = X2) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f80,f22])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X3) | r3_lattice3(sK0,sK3(sK0,X2,X3),X3) | k16_lattice3(sK0,X3) = X2) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f73,f21])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X2,X3] : (v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,X3) | r3_lattice3(sK0,sK3(sK0,X2,X3),X3) | k16_lattice3(sK0,X3) = X2) )),
% 0.20/0.48    inference(resolution,[],[f23,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | r3_lattice3(X0,sK3(X0,X1,X2),X2) | k16_lattice3(X0,X2) = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r3_lattice3(X0,X1,sK2) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(sK1,u1_struct_0(X0)) | r1_lattices(X0,X1,sK1) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(resolution,[],[f17,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X1,X3) | ~r3_lattice3(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    r2_hidden(sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (13809)------------------------------
% 0.20/0.48  % (13809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (13809)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (13809)Memory used [KB]: 1663
% 0.20/0.48  % (13809)Time elapsed: 0.068 s
% 0.20/0.48  % (13809)------------------------------
% 0.20/0.48  % (13809)------------------------------
% 0.20/0.48  % (13795)Success in time 0.126 s
%------------------------------------------------------------------------------
