%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 290 expanded)
%              Number of leaves         :    5 (  50 expanded)
%              Depth                    :   32
%              Number of atoms          :  394 (1694 expanded)
%              Number of equality atoms :   52 (  58 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(resolution,[],[f317,f148])).

fof(f148,plain,(
    ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f147,f17])).

fof(f17,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
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
                ( r3_lattice3(X0,X1,X2)
               => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
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
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

fof(f147,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f146,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f146,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f145,f23])).

fof(f23,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f145,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f144,f22])).

fof(f22,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f144,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f143,f21])).

fof(f21,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f143,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f139,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f139,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r3_lattice3(sK0,sK1,sK2) ),
    inference(resolution,[],[f18,f42])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,k16_lattice3(X0,X2)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
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
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f18,plain,(
    ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f317,plain,(
    ! [X0] : m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f298,f117])).

fof(f117,plain,(
    ! [X6] : k16_lattice3(sK0,X6) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X6)) ),
    inference(subsumption_resolution,[],[f112,f20])).

fof(f112,plain,(
    ! [X6] :
      ( v2_struct_0(sK0)
      | k16_lattice3(sK0,X6) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X6)) ) ),
    inference(resolution,[],[f23,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

fof(f298,plain,(
    ! [X2] : m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f297,f22])).

fof(f297,plain,(
    ! [X2] :
      ( m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f296,f23])).

fof(f296,plain,(
    ! [X2] :
      ( m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f291,f20])).

fof(f291,plain,(
    ! [X2] :
      ( m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0) ) ),
    inference(superposition,[],[f38,f270])).

fof(f270,plain,(
    ! [X0] : k15_lattice3(sK0,X0) = sK6(sK0,X0) ),
    inference(subsumption_resolution,[],[f269,f22])).

fof(f269,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f268,f23])).

fof(f268,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f267,f20])).

fof(f267,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0) ) ),
    inference(resolution,[],[f266,f38])).

fof(f266,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | k15_lattice3(sK0,X0) = sK6(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f265,f22])).

fof(f265,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f264,f23])).

fof(f264,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f263,f20])).

fof(f263,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0) ) ),
    inference(resolution,[],[f262,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | r4_lattice3(X0,sK6(X0,X1),X1)
      | ~ v4_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r4_lattice3(X0,X3,X1)
                 => r1_lattices(X0,X2,X3) ) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattice3)).

fof(f262,plain,(
    ! [X0] :
      ( ~ r4_lattice3(sK0,sK6(sK0,X0),X0)
      | k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | ~ r4_lattice3(sK0,sK6(sK0,X0),X0)
      | k15_lattice3(sK0,X0) = sK6(sK0,X0) ) ),
    inference(resolution,[],[f201,f240])).

fof(f240,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0)
      | k15_lattice3(sK0,X0) = sK6(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f239,f22])).

fof(f239,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0)
      | k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f238,f23])).

fof(f238,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0)
      | k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f20])).

fof(f237,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0)
      | k15_lattice3(sK0,X0) = sK6(sK0,X0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0) ) ),
    inference(resolution,[],[f195,f38])).

fof(f195,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK6(sK0,X3),u1_struct_0(sK0))
      | r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X3)),X3)
      | k15_lattice3(sK0,X3) = sK6(sK0,X3) ) ),
    inference(subsumption_resolution,[],[f194,f22])).

% (29386)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (29383)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (29382)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (29381)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (29394)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (29393)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (29395)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f194,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK6(sK0,X3),u1_struct_0(sK0))
      | r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X3)),X3)
      | k15_lattice3(sK0,X3) = sK6(sK0,X3)
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f23])).

fof(f193,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK6(sK0,X3),u1_struct_0(sK0))
      | r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X3)),X3)
      | k15_lattice3(sK0,X3) = sK6(sK0,X3)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f191,f20])).

fof(f191,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK6(sK0,X3),u1_struct_0(sK0))
      | r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X3)),X3)
      | k15_lattice3(sK0,X3) = sK6(sK0,X3)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0) ) ),
    inference(resolution,[],[f77,f39])).

fof(f77,plain,(
    ! [X8,X9] :
      ( ~ r4_lattice3(sK0,X8,X9)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | r4_lattice3(sK0,sK4(sK0,X9,X8),X9)
      | k15_lattice3(sK0,X9) = X8 ) ),
    inference(subsumption_resolution,[],[f76,f23])).

fof(f76,plain,(
    ! [X8,X9] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X8,X9)
      | r4_lattice3(sK0,sK4(sK0,X9,X8),X9)
      | k15_lattice3(sK0,X9) = X8 ) ),
    inference(subsumption_resolution,[],[f75,f22])).

fof(f75,plain,(
    ! [X8,X9] :
      ( ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X8,X9)
      | r4_lattice3(sK0,sK4(sK0,X9,X8),X9)
      | k15_lattice3(sK0,X9) = X8 ) ),
    inference(subsumption_resolution,[],[f66,f20])).

fof(f66,plain,(
    ! [X8,X9] :
      ( v2_struct_0(sK0)
      | ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X8,X9)
      | r4_lattice3(sK0,sK4(sK0,X9,X8),X9)
      | k15_lattice3(sK0,X9) = X8 ) ),
    inference(resolution,[],[f21,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | r4_lattice3(X0,sK4(X0,X1,X2),X1)
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(f201,plain,(
    ! [X2,X3] :
      ( ~ r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X2)),X2)
      | ~ m1_subset_1(sK6(sK0,X2),u1_struct_0(sK0))
      | sK6(sK0,X2) = k15_lattice3(sK0,X3)
      | ~ r4_lattice3(sK0,sK6(sK0,X2),X3) ) ),
    inference(subsumption_resolution,[],[f200,f74])).

fof(f74,plain,(
    ! [X6,X7] :
      ( ~ r4_lattice3(sK0,X6,X7)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0))
      | k15_lattice3(sK0,X7) = X6 ) ),
    inference(subsumption_resolution,[],[f73,f23])).

fof(f73,plain,(
    ! [X6,X7] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X6,X7)
      | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0))
      | k15_lattice3(sK0,X7) = X6 ) ),
    inference(subsumption_resolution,[],[f72,f22])).

fof(f72,plain,(
    ! [X6,X7] :
      ( ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X6,X7)
      | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0))
      | k15_lattice3(sK0,X7) = X6 ) ),
    inference(subsumption_resolution,[],[f65,f20])).

fof(f65,plain,(
    ! [X6,X7] :
      ( v2_struct_0(sK0)
      | ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X6,X7)
      | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0))
      | k15_lattice3(sK0,X7) = X6 ) ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f200,plain,(
    ! [X2,X3] :
      ( ~ r4_lattice3(sK0,sK6(sK0,X2),X3)
      | ~ m1_subset_1(sK6(sK0,X2),u1_struct_0(sK0))
      | sK6(sK0,X2) = k15_lattice3(sK0,X3)
      | ~ m1_subset_1(sK4(sK0,X3,sK6(sK0,X2)),u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X2)),X2) ) ),
    inference(subsumption_resolution,[],[f199,f22])).

fof(f199,plain,(
    ! [X2,X3] :
      ( ~ r4_lattice3(sK0,sK6(sK0,X2),X3)
      | ~ m1_subset_1(sK6(sK0,X2),u1_struct_0(sK0))
      | sK6(sK0,X2) = k15_lattice3(sK0,X3)
      | ~ m1_subset_1(sK4(sK0,X3,sK6(sK0,X2)),u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X2)),X2)
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f198,f23])).

fof(f198,plain,(
    ! [X2,X3] :
      ( ~ r4_lattice3(sK0,sK6(sK0,X2),X3)
      | ~ m1_subset_1(sK6(sK0,X2),u1_struct_0(sK0))
      | sK6(sK0,X2) = k15_lattice3(sK0,X3)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK4(sK0,X3,sK6(sK0,X2)),u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X2)),X2)
      | ~ v4_lattice3(sK0) ) ),
    inference(subsumption_resolution,[],[f197,f20])).

fof(f197,plain,(
    ! [X2,X3] :
      ( ~ r4_lattice3(sK0,sK6(sK0,X2),X3)
      | ~ m1_subset_1(sK6(sK0,X2),u1_struct_0(sK0))
      | sK6(sK0,X2) = k15_lattice3(sK0,X3)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK4(sK0,X3,sK6(sK0,X2)),u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X2)),X2)
      | ~ v4_lattice3(sK0) ) ),
    inference(resolution,[],[f80,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,sK6(X0,X1),X3)
      | ~ v4_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X10,X11] :
      ( ~ r1_lattices(sK0,X10,sK4(sK0,X11,X10))
      | ~ r4_lattice3(sK0,X10,X11)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | k15_lattice3(sK0,X11) = X10 ) ),
    inference(subsumption_resolution,[],[f79,f23])).

fof(f79,plain,(
    ! [X10,X11] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X10,X11)
      | ~ r1_lattices(sK0,X10,sK4(sK0,X11,X10))
      | k15_lattice3(sK0,X11) = X10 ) ),
    inference(subsumption_resolution,[],[f78,f22])).

fof(f78,plain,(
    ! [X10,X11] :
      ( ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X10,X11)
      | ~ r1_lattices(sK0,X10,sK4(sK0,X11,X10))
      | k15_lattice3(sK0,X11) = X10 ) ),
    inference(subsumption_resolution,[],[f67,f20])).

fof(f67,plain,(
    ! [X10,X11] :
      ( v2_struct_0(sK0)
      | ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X10,X11)
      | ~ r1_lattices(sK0,X10,sK4(sK0,X11,X10))
      | k15_lattice3(sK0,X11) = X10 ) ),
    inference(resolution,[],[f21,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ v4_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (29379)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (29379)Refutation not found, incomplete strategy% (29379)------------------------------
% 0.21/0.47  % (29379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29385)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (29392)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (29379)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (29379)Memory used [KB]: 10618
% 0.21/0.47  % (29379)Time elapsed: 0.050 s
% 0.21/0.47  % (29379)------------------------------
% 0.21/0.47  % (29379)------------------------------
% 0.21/0.48  % (29378)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (29384)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (29391)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (29387)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (29391)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(resolution,[],[f317,f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f147,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    r3_lattice3(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f146,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f145,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    l3_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f144,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v4_lattice3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f143,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    v10_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f139,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK1,sK2)),
% 0.21/0.49    inference(resolution,[],[f18,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X3] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,k16_lattice3(X0,X2))) )),
% 0.21/0.49    inference(equality_resolution,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,X1) | k16_lattice3(X0,X2) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ~r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 0.21/0.49    inference(superposition,[],[f298,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ( ! [X6] : (k16_lattice3(sK0,X6) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X6))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f20])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X6] : (v2_struct_0(sK0) | k16_lattice3(sK0,X6) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X6))) )),
% 0.21/0.49    inference(resolution,[],[f23,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    ( ! [X2] : (m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f297,f22])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    ( ! [X2] : (m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f296,f23])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    ( ! [X2] : (m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f291,f20])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    ( ! [X2] : (m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(superposition,[],[f38,f270])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    ( ! [X0] : (k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f269,f22])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ( ! [X0] : (k15_lattice3(sK0,X0) = sK6(sK0,X0) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f268,f23])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ( ! [X0] : (k15_lattice3(sK0,X0) = sK6(sK0,X0) | ~l3_lattices(sK0) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f267,f20])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ( ! [X0] : (k15_lattice3(sK0,X0) = sK6(sK0,X0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f266,f38])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f265,f22])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ( ! [X0] : (k15_lattice3(sK0,X0) = sK6(sK0,X0) | ~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f264,f23])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    ( ! [X0] : (k15_lattice3(sK0,X0) = sK6(sK0,X0) | ~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f263,f20])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    ( ! [X0] : (k15_lattice3(sK0,X0) = sK6(sK0,X0) | ~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f262,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | r4_lattice3(X0,sK6(X0,X1),X1) | ~v4_lattice3(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattice3)).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ( ! [X0] : (~r4_lattice3(sK0,sK6(sK0,X0),X0) | k15_lattice3(sK0,X0) = sK6(sK0,X0) | ~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f260])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = sK6(sK0,X0) | ~r4_lattice3(sK0,sK6(sK0,X0),X0) | k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.21/0.49    inference(resolution,[],[f201,f240])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ( ! [X0] : (r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0) | k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f239,f22])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    ( ! [X0] : (r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0) | k15_lattice3(sK0,X0) = sK6(sK0,X0) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f238,f23])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    ( ! [X0] : (r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0) | k15_lattice3(sK0,X0) = sK6(sK0,X0) | ~l3_lattices(sK0) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f237,f20])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ( ! [X0] : (r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0) | k15_lattice3(sK0,X0) = sK6(sK0,X0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~v4_lattice3(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f195,f38])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X3] : (~m1_subset_1(sK6(sK0,X3),u1_struct_0(sK0)) | r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X3)),X3) | k15_lattice3(sK0,X3) = sK6(sK0,X3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f194,f22])).
% 0.21/0.49  % (29386)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (29383)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (29382)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (29381)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (29394)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (29393)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (29395)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X3] : (~m1_subset_1(sK6(sK0,X3),u1_struct_0(sK0)) | r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X3)),X3) | k15_lattice3(sK0,X3) = sK6(sK0,X3) | ~v4_lattice3(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f193,f23])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ( ! [X3] : (~m1_subset_1(sK6(sK0,X3),u1_struct_0(sK0)) | r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X3)),X3) | k15_lattice3(sK0,X3) = sK6(sK0,X3) | ~l3_lattices(sK0) | ~v4_lattice3(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f191,f20])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X3] : (~m1_subset_1(sK6(sK0,X3),u1_struct_0(sK0)) | r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X3)),X3) | k15_lattice3(sK0,X3) = sK6(sK0,X3) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~v4_lattice3(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f77,f39])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X8,X9] : (~r4_lattice3(sK0,X8,X9) | ~m1_subset_1(X8,u1_struct_0(sK0)) | r4_lattice3(sK0,sK4(sK0,X9,X8),X9) | k15_lattice3(sK0,X9) = X8) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f76,f23])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X8,X9] : (~l3_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X8,X9) | r4_lattice3(sK0,sK4(sK0,X9,X8),X9) | k15_lattice3(sK0,X9) = X8) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f75,f22])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X8,X9] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X8,X9) | r4_lattice3(sK0,sK4(sK0,X9,X8),X9) | k15_lattice3(sK0,X9) = X8) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f66,f20])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X8,X9] : (v2_struct_0(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X8,X9) | r4_lattice3(sK0,sK4(sK0,X9,X8),X9) | k15_lattice3(sK0,X9) = X8) )),
% 0.21/0.50    inference(resolution,[],[f21,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | r4_lattice3(X0,sK4(X0,X1,X2),X1) | k15_lattice3(X0,X1) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X2)),X2) | ~m1_subset_1(sK6(sK0,X2),u1_struct_0(sK0)) | sK6(sK0,X2) = k15_lattice3(sK0,X3) | ~r4_lattice3(sK0,sK6(sK0,X2),X3)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f200,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X6,X7] : (~r4_lattice3(sK0,X6,X7) | ~m1_subset_1(X6,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X7) = X6) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f73,f23])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X6,X7] : (~l3_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X6,X7) | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X7) = X6) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f72,f22])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X6,X7] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X6,X7) | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X7) = X6) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f65,f20])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X6,X7] : (v2_struct_0(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X6,X7) | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X7) = X6) )),
% 0.21/0.50    inference(resolution,[],[f21,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | k15_lattice3(X0,X1) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r4_lattice3(sK0,sK6(sK0,X2),X3) | ~m1_subset_1(sK6(sK0,X2),u1_struct_0(sK0)) | sK6(sK0,X2) = k15_lattice3(sK0,X3) | ~m1_subset_1(sK4(sK0,X3,sK6(sK0,X2)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X2)),X2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f199,f22])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r4_lattice3(sK0,sK6(sK0,X2),X3) | ~m1_subset_1(sK6(sK0,X2),u1_struct_0(sK0)) | sK6(sK0,X2) = k15_lattice3(sK0,X3) | ~m1_subset_1(sK4(sK0,X3,sK6(sK0,X2)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X2)),X2) | ~v4_lattice3(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f198,f23])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r4_lattice3(sK0,sK6(sK0,X2),X3) | ~m1_subset_1(sK6(sK0,X2),u1_struct_0(sK0)) | sK6(sK0,X2) = k15_lattice3(sK0,X3) | ~l3_lattices(sK0) | ~m1_subset_1(sK4(sK0,X3,sK6(sK0,X2)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X2)),X2) | ~v4_lattice3(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f197,f20])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r4_lattice3(sK0,sK6(sK0,X2),X3) | ~m1_subset_1(sK6(sK0,X2),u1_struct_0(sK0)) | sK6(sK0,X2) = k15_lattice3(sK0,X3) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK4(sK0,X3,sK6(sK0,X2)),u1_struct_0(sK0)) | ~r4_lattice3(sK0,sK4(sK0,X3,sK6(sK0,X2)),X2) | ~v4_lattice3(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f80,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,sK6(X0,X1),X3) | ~v4_lattice3(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X10,X11] : (~r1_lattices(sK0,X10,sK4(sK0,X11,X10)) | ~r4_lattice3(sK0,X10,X11) | ~m1_subset_1(X10,u1_struct_0(sK0)) | k15_lattice3(sK0,X11) = X10) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f79,f23])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X10,X11] : (~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X10,X11) | ~r1_lattices(sK0,X10,sK4(sK0,X11,X10)) | k15_lattice3(sK0,X11) = X10) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f78,f22])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X10,X11] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X10,X11) | ~r1_lattices(sK0,X10,sK4(sK0,X11,X10)) | k15_lattice3(sK0,X11) = X10) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f67,f20])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X10,X11] : (v2_struct_0(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X10,X11) | ~r1_lattices(sK0,X10,sK4(sK0,X11,X10)) | k15_lattice3(sK0,X11) = X10) )),
% 0.21/0.50    inference(resolution,[],[f21,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~r1_lattices(X0,X2,sK4(X0,X1,X2)) | k15_lattice3(X0,X1) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) | ~v4_lattice3(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (29391)------------------------------
% 0.21/0.50  % (29391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29391)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (29391)Memory used [KB]: 1663
% 0.21/0.50  % (29391)Time elapsed: 0.046 s
% 0.21/0.50  % (29391)------------------------------
% 0.21/0.50  % (29391)------------------------------
% 0.21/0.50  % (29397)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (29377)Success in time 0.147 s
%------------------------------------------------------------------------------
