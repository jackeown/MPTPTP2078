%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 645 expanded)
%              Number of leaves         :    9 ( 112 expanded)
%              Depth                    :   39
%              Number of atoms          :  663 (4009 expanded)
%              Number of equality atoms :   31 (  37 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f855,plain,(
    $false ),
    inference(subsumption_resolution,[],[f850,f591])).

fof(f591,plain,(
    r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    inference(backward_demodulation,[],[f311,f557])).

fof(f557,plain,(
    ! [X0] : k15_lattice3(sK0,X0) = sK6(sK0,X0) ),
    inference(subsumption_resolution,[],[f556,f534])).

fof(f534,plain,(
    ! [X2] :
      ( r1_lattices(sK0,sK6(sK0,X2),sK4(sK0,X2,sK6(sK0,X2)))
      | sK6(sK0,X2) = k15_lattice3(sK0,X2) ) ),
    inference(subsumption_resolution,[],[f522,f467])).

fof(f467,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK0,X0,sK6(sK0,X0)),u1_struct_0(sK0))
      | k15_lattice3(sK0,X0) = sK6(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f456,f156])).

fof(f156,plain,(
    ! [X14] : m1_subset_1(sK6(sK0,X14),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f155,f35])).

fof(f35,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
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
              ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
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
                ( r2_hidden(X1,X2)
               => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                  & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
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
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

fof(f155,plain,(
    ! [X14] :
      ( ~ l3_lattices(sK0)
      | m1_subset_1(sK6(sK0,X14),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f129,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f129,plain,(
    ! [X14] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | m1_subset_1(sK6(sK0,X14),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f34,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ v4_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).

fof(f34,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f456,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,X0,sK6(sK0,X0)),u1_struct_0(sK0))
      | k15_lattice3(sK0,X0) = sK6(sK0,X0) ) ),
    inference(resolution,[],[f146,f158])).

% (22205)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f158,plain,(
    ! [X15] : r4_lattice3(sK0,sK6(sK0,X15),X15) ),
    inference(subsumption_resolution,[],[f157,f35])).

% (22190)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f157,plain,(
    ! [X15] :
      ( ~ l3_lattices(sK0)
      | r4_lattice3(sK0,sK6(sK0,X15),X15) ) ),
    inference(subsumption_resolution,[],[f130,f32])).

fof(f130,plain,(
    ! [X15] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | r4_lattice3(sK0,sK6(sK0,X15),X15) ) ),
    inference(resolution,[],[f34,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | r4_lattice3(X0,sK6(X0,X1),X1)
      | ~ v4_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f146,plain,(
    ! [X6,X7] :
      ( ~ r4_lattice3(sK0,X6,X7)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0))
      | k15_lattice3(sK0,X7) = X6 ) ),
    inference(subsumption_resolution,[],[f145,f35])).

fof(f145,plain,(
    ! [X6,X7] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X6,X7)
      | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0))
      | k15_lattice3(sK0,X7) = X6 ) ),
    inference(subsumption_resolution,[],[f144,f33])).

fof(f33,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f144,plain,(
    ! [X6,X7] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X6,X7)
      | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0))
      | k15_lattice3(sK0,X7) = X6 ) ),
    inference(subsumption_resolution,[],[f125,f32])).

fof(f125,plain,(
    ! [X6,X7] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X6,X7)
      | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0))
      | k15_lattice3(sK0,X7) = X6 ) ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f522,plain,(
    ! [X2] :
      ( sK6(sK0,X2) = k15_lattice3(sK0,X2)
      | ~ m1_subset_1(sK4(sK0,X2,sK6(sK0,X2)),u1_struct_0(sK0))
      | r1_lattices(sK0,sK6(sK0,X2),sK4(sK0,X2,sK6(sK0,X2))) ) ),
    inference(resolution,[],[f485,f154])).

% (22196)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f154,plain,(
    ! [X12,X13] :
      ( ~ r4_lattice3(sK0,X12,X13)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | r1_lattices(sK0,sK6(sK0,X13),X12) ) ),
    inference(subsumption_resolution,[],[f153,f35])).

fof(f153,plain,(
    ! [X12,X13] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X12,X13)
      | r1_lattices(sK0,sK6(sK0,X13),X12) ) ),
    inference(subsumption_resolution,[],[f128,f32])).

fof(f128,plain,(
    ! [X12,X13] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X12,X13)
      | r1_lattices(sK0,sK6(sK0,X13),X12) ) ),
    inference(resolution,[],[f34,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,sK6(X0,X1),X3)
      | ~ v4_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f485,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0)
      | k15_lattice3(sK0,X0) = sK6(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f474,f156])).

fof(f474,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0)
      | k15_lattice3(sK0,X0) = sK6(sK0,X0) ) ),
    inference(resolution,[],[f149,f158])).

fof(f149,plain,(
    ! [X8,X9] :
      ( ~ r4_lattice3(sK0,X8,X9)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | r4_lattice3(sK0,sK4(sK0,X9,X8),X9)
      | k15_lattice3(sK0,X9) = X8 ) ),
    inference(subsumption_resolution,[],[f148,f35])).

fof(f148,plain,(
    ! [X8,X9] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X8,X9)
      | r4_lattice3(sK0,sK4(sK0,X9,X8),X9)
      | k15_lattice3(sK0,X9) = X8 ) ),
    inference(subsumption_resolution,[],[f147,f33])).

fof(f147,plain,(
    ! [X8,X9] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X8,X9)
      | r4_lattice3(sK0,sK4(sK0,X9,X8),X9)
      | k15_lattice3(sK0,X9) = X8 ) ),
    inference(subsumption_resolution,[],[f126,f32])).

fof(f126,plain,(
    ! [X8,X9] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X8,X9)
      | r4_lattice3(sK0,sK4(sK0,X9,X8),X9)
      | k15_lattice3(sK0,X9) = X8 ) ),
    inference(resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | r4_lattice3(X0,sK4(X0,X1,X2),X1)
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f556,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK0,sK6(sK0,X0),sK4(sK0,X0,sK6(sK0,X0)))
      | k15_lattice3(sK0,X0) = sK6(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f544,f156])).

fof(f544,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | ~ r1_lattices(sK0,sK6(sK0,X0),sK4(sK0,X0,sK6(sK0,X0)))
      | k15_lattice3(sK0,X0) = sK6(sK0,X0) ) ),
    inference(resolution,[],[f152,f158])).

fof(f152,plain,(
    ! [X10,X11] :
      ( ~ r4_lattice3(sK0,X10,X11)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X10,sK4(sK0,X11,X10))
      | k15_lattice3(sK0,X11) = X10 ) ),
    inference(subsumption_resolution,[],[f151,f35])).

fof(f151,plain,(
    ! [X10,X11] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X10,X11)
      | ~ r1_lattices(sK0,X10,sK4(sK0,X11,X10))
      | k15_lattice3(sK0,X11) = X10 ) ),
    inference(subsumption_resolution,[],[f150,f33])).

fof(f150,plain,(
    ! [X10,X11] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X10,X11)
      | ~ r1_lattices(sK0,X10,sK4(sK0,X11,X10))
      | k15_lattice3(sK0,X11) = X10 ) ),
    inference(subsumption_resolution,[],[f127,f32])).

fof(f127,plain,(
    ! [X10,X11] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X10,X11)
      | ~ r1_lattices(sK0,X10,sK4(sK0,X11,X10))
      | k15_lattice3(sK0,X11) = X10 ) ),
    inference(resolution,[],[f34,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | k15_lattice3(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f311,plain,(
    r3_lattices(sK0,sK1,sK6(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f310,f33])).

fof(f310,plain,
    ( r3_lattices(sK0,sK1,sK6(sK0,sK2))
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f309,f32])).

fof(f309,plain,
    ( r3_lattices(sK0,sK1,sK6(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f308,f35])).

fof(f308,plain,
    ( r3_lattices(sK0,sK1,sK6(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f307,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f307,plain,
    ( ~ v6_lattices(sK0)
    | r3_lattices(sK0,sK1,sK6(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f306,f33])).

fof(f306,plain,
    ( ~ v6_lattices(sK0)
    | r3_lattices(sK0,sK1,sK6(sK0,sK2))
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f305,f32])).

fof(f305,plain,
    ( ~ v6_lattices(sK0)
    | r3_lattices(sK0,sK1,sK6(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f304,f35])).

fof(f304,plain,
    ( ~ v6_lattices(sK0)
    | r3_lattices(sK0,sK1,sK6(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f303,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f303,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,sK1,sK6(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f302,f33])).

fof(f302,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,sK1,sK6(sK0,sK2))
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f301,f32])).

fof(f301,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,sK1,sK6(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f300,f35])).

fof(f300,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,sK1,sK6(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f299,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f299,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,sK1,sK6(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f298,f156])).

fof(f298,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(sK6(sK0,sK2),u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,sK6(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f297,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f297,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK2),u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,sK6(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f296,f35])).

fof(f296,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK2),u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,sK6(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f295,f32])).

fof(f295,plain,
    ( v2_struct_0(sK0)
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK2),u1_struct_0(sK0))
    | r3_lattices(sK0,sK1,sK6(sK0,sK2)) ),
    inference(resolution,[],[f294,f67])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f294,plain,(
    r1_lattices(sK0,sK1,sK6(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f293,f31])).

fof(f293,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,sK6(sK0,sK2)) ),
    inference(resolution,[],[f269,f30])).

fof(f30,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f269,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,sK6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f268,f156])).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r1_lattices(sK0,X1,sK6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f267,f35])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r1_lattices(sK0,X1,sK6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f258,f32])).

fof(f258,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r1_lattices(sK0,X1,sK6(sK0,X0)) ) ),
    inference(resolution,[],[f158,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X3,X1)
      | ~ r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f850,plain,(
    ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f838,f29])).

fof(f29,plain,
    ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f838,plain,(
    r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f837,f33])).

fof(f837,plain,
    ( r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f836,f32])).

fof(f836,plain,
    ( r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f835,f35])).

fof(f835,plain,
    ( r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f834,f38])).

fof(f834,plain,
    ( ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f833,f33])).

fof(f833,plain,
    ( ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f832,f32])).

fof(f832,plain,
    ( ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f831,f35])).

fof(f831,plain,
    ( ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f830,f40])).

fof(f830,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f829,f33])).

fof(f829,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f828,f32])).

fof(f828,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(subsumption_resolution,[],[f827,f35])).

fof(f827,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v10_lattices(sK0) ),
    inference(resolution,[],[f826,f41])).

fof(f826,plain,
    ( ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f825,f35])).

fof(f825,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f821,f32])).

fof(f821,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f819,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f819,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v6_lattices(sK0)
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f818,f31])).

fof(f818,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f817,f35])).

fof(f817,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f813,f32])).

fof(f813,plain,
    ( v2_struct_0(sK0)
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(resolution,[],[f812,f67])).

% (22190)Refutation not found, incomplete strategy% (22190)------------------------------
% (22190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22190)Termination reason: Refutation not found, incomplete strategy

% (22190)Memory used [KB]: 10618
% (22190)Time elapsed: 0.100 s
% (22190)------------------------------
% (22190)------------------------------
fof(f812,plain,(
    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f811,f35])).

fof(f811,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f807,f32])).

fof(f807,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f806,f66])).

fof(f806,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f805,f32])).

fof(f805,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f804,f31])).

fof(f804,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f801,f35])).

fof(f801,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f205,f279])).

fof(f279,plain,(
    ! [X0] : r3_lattice3(sK0,k16_lattice3(sK0,X0),X0) ),
    inference(subsumption_resolution,[],[f278,f35])).

fof(f278,plain,(
    ! [X0] :
      ( r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f274,f32])).

fof(f274,plain,(
    ! [X0] :
      ( r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f161,f66])).

fof(f161,plain,(
    ! [X16] :
      ( ~ m1_subset_1(k16_lattice3(sK0,X16),u1_struct_0(sK0))
      | r3_lattice3(sK0,k16_lattice3(sK0,X16),X16) ) ),
    inference(subsumption_resolution,[],[f160,f35])).

fof(f160,plain,(
    ! [X16] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(k16_lattice3(sK0,X16),u1_struct_0(sK0))
      | r3_lattice3(sK0,k16_lattice3(sK0,X16),X16) ) ),
    inference(subsumption_resolution,[],[f159,f33])).

fof(f159,plain,(
    ! [X16] :
      ( ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(k16_lattice3(sK0,X16),u1_struct_0(sK0))
      | r3_lattice3(sK0,k16_lattice3(sK0,X16),X16) ) ),
    inference(subsumption_resolution,[],[f131,f32])).

fof(f131,plain,(
    ! [X16] :
      ( v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(k16_lattice3(sK0,X16),u1_struct_0(sK0))
      | r3_lattice3(sK0,k16_lattice3(sK0,X16),X16) ) ),
    inference(resolution,[],[f34,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | r3_lattice3(X0,k16_lattice3(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f205,plain,(
    ! [X2,X3] :
      ( ~ r3_lattice3(X2,X3,sK2)
      | ~ l3_lattices(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(sK1,u1_struct_0(X2))
      | r1_lattices(X2,X3,sK1)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f30,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X1,X3)
      | ~ r3_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:00:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (22194)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (22201)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (22202)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (22193)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (22202)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (22204)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (22191)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f855,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f850,f591])).
% 0.22/0.51  fof(f591,plain,(
% 0.22/0.51    r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))),
% 0.22/0.51    inference(backward_demodulation,[],[f311,f557])).
% 0.22/0.51  fof(f557,plain,(
% 0.22/0.51    ( ! [X0] : (k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f556,f534])).
% 0.22/0.51  fof(f534,plain,(
% 0.22/0.51    ( ! [X2] : (r1_lattices(sK0,sK6(sK0,X2),sK4(sK0,X2,sK6(sK0,X2))) | sK6(sK0,X2) = k15_lattice3(sK0,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f522,f467])).
% 0.22/0.51  fof(f467,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK4(sK0,X0,sK6(sK0,X0)),u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f456,f156])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    ( ! [X14] : (m1_subset_1(sK6(sK0,X14),u1_struct_0(sK0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f155,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    l3_lattices(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    ( ! [X14] : (~l3_lattices(sK0) | m1_subset_1(sK6(sK0,X14),u1_struct_0(sK0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f129,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    ( ! [X14] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | m1_subset_1(sK6(sK0,X14),u1_struct_0(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f34,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) | ~v4_lattice3(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    v4_lattice3(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f456,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | m1_subset_1(sK4(sK0,X0,sK6(sK0,X0)),u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.22/0.51    inference(resolution,[],[f146,f158])).
% 0.22/0.51  % (22205)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ( ! [X15] : (r4_lattice3(sK0,sK6(sK0,X15),X15)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f157,f35])).
% 0.22/0.51  % (22190)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ( ! [X15] : (~l3_lattices(sK0) | r4_lattice3(sK0,sK6(sK0,X15),X15)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f130,f32])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ( ! [X15] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | r4_lattice3(sK0,sK6(sK0,X15),X15)) )),
% 0.22/0.51    inference(resolution,[],[f34,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | r4_lattice3(X0,sK6(X0,X1),X1) | ~v4_lattice3(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~r4_lattice3(sK0,X6,X7) | ~m1_subset_1(X6,u1_struct_0(sK0)) | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X7) = X6) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f145,f35])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~l3_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X6,X7) | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X7) = X6) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f144,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    v10_lattices(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ( ! [X6,X7] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X6,X7) | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X7) = X6) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f125,f32])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ( ! [X6,X7] : (v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X6,X7) | m1_subset_1(sK4(sK0,X7,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X7) = X6) )),
% 0.22/0.51    inference(resolution,[],[f34,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | k15_lattice3(X0,X1) = X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 0.22/0.51  fof(f522,plain,(
% 0.22/0.51    ( ! [X2] : (sK6(sK0,X2) = k15_lattice3(sK0,X2) | ~m1_subset_1(sK4(sK0,X2,sK6(sK0,X2)),u1_struct_0(sK0)) | r1_lattices(sK0,sK6(sK0,X2),sK4(sK0,X2,sK6(sK0,X2)))) )),
% 0.22/0.51    inference(resolution,[],[f485,f154])).
% 0.22/0.51  % (22196)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ( ! [X12,X13] : (~r4_lattice3(sK0,X12,X13) | ~m1_subset_1(X12,u1_struct_0(sK0)) | r1_lattices(sK0,sK6(sK0,X13),X12)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f153,f35])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ( ! [X12,X13] : (~l3_lattices(sK0) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X12,X13) | r1_lattices(sK0,sK6(sK0,X13),X12)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f128,f32])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    ( ! [X12,X13] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X12,X13) | r1_lattices(sK0,sK6(sK0,X13),X12)) )),
% 0.22/0.51    inference(resolution,[],[f34,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,sK6(X0,X1),X3) | ~v4_lattice3(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f485,plain,(
% 0.22/0.51    ( ! [X0] : (r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0) | k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f474,f156])).
% 0.22/0.51  fof(f474,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | r4_lattice3(sK0,sK4(sK0,X0,sK6(sK0,X0)),X0) | k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.22/0.51    inference(resolution,[],[f149,f158])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    ( ! [X8,X9] : (~r4_lattice3(sK0,X8,X9) | ~m1_subset_1(X8,u1_struct_0(sK0)) | r4_lattice3(sK0,sK4(sK0,X9,X8),X9) | k15_lattice3(sK0,X9) = X8) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f35])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ( ! [X8,X9] : (~l3_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X8,X9) | r4_lattice3(sK0,sK4(sK0,X9,X8),X9) | k15_lattice3(sK0,X9) = X8) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f147,f33])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    ( ! [X8,X9] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X8,X9) | r4_lattice3(sK0,sK4(sK0,X9,X8),X9) | k15_lattice3(sK0,X9) = X8) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f126,f32])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X8,X9] : (v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X8,X9) | r4_lattice3(sK0,sK4(sK0,X9,X8),X9) | k15_lattice3(sK0,X9) = X8) )),
% 0.22/0.51    inference(resolution,[],[f34,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | r4_lattice3(X0,sK4(X0,X1,X2),X1) | k15_lattice3(X0,X1) = X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f556,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_lattices(sK0,sK6(sK0,X0),sK4(sK0,X0,sK6(sK0,X0))) | k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f544,f156])).
% 0.22/0.51  fof(f544,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | ~r1_lattices(sK0,sK6(sK0,X0),sK4(sK0,X0,sK6(sK0,X0))) | k15_lattice3(sK0,X0) = sK6(sK0,X0)) )),
% 0.22/0.51    inference(resolution,[],[f152,f158])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ( ! [X10,X11] : (~r4_lattice3(sK0,X10,X11) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r1_lattices(sK0,X10,sK4(sK0,X11,X10)) | k15_lattice3(sK0,X11) = X10) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f151,f35])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ( ! [X10,X11] : (~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X10,X11) | ~r1_lattices(sK0,X10,sK4(sK0,X11,X10)) | k15_lattice3(sK0,X11) = X10) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f150,f33])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ( ! [X10,X11] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X10,X11) | ~r1_lattices(sK0,X10,sK4(sK0,X11,X10)) | k15_lattice3(sK0,X11) = X10) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f127,f32])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ( ! [X10,X11] : (v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X10,X11) | ~r1_lattices(sK0,X10,sK4(sK0,X11,X10)) | k15_lattice3(sK0,X11) = X10) )),
% 0.22/0.51    inference(resolution,[],[f34,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~r1_lattices(X0,X2,sK4(X0,X1,X2)) | k15_lattice3(X0,X1) = X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f311,plain,(
% 0.22/0.51    r3_lattices(sK0,sK1,sK6(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f310,f33])).
% 0.22/0.51  fof(f310,plain,(
% 0.22/0.51    r3_lattices(sK0,sK1,sK6(sK0,sK2)) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f309,f32])).
% 0.22/0.51  fof(f309,plain,(
% 0.22/0.51    r3_lattices(sK0,sK1,sK6(sK0,sK2)) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f308,f35])).
% 0.22/0.51  fof(f308,plain,(
% 0.22/0.51    r3_lattices(sK0,sK1,sK6(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f307,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v6_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.51  fof(f307,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r3_lattices(sK0,sK1,sK6(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f306,f33])).
% 0.22/0.51  fof(f306,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r3_lattices(sK0,sK1,sK6(sK0,sK2)) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f305,f32])).
% 0.22/0.51  fof(f305,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r3_lattices(sK0,sK1,sK6(sK0,sK2)) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f304,f35])).
% 0.22/0.51  fof(f304,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r3_lattices(sK0,sK1,sK6(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f303,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v8_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f303,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,sK1,sK6(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f302,f33])).
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,sK1,sK6(sK0,sK2)) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f301,f32])).
% 0.22/0.51  fof(f301,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,sK1,sK6(sK0,sK2)) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f300,f35])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,sK1,sK6(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f299,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v9_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f299,plain,(
% 0.22/0.51    ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,sK1,sK6(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f298,f156])).
% 0.22/0.51  fof(f298,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(sK6(sK0,sK2),u1_struct_0(sK0)) | r3_lattices(sK0,sK1,sK6(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f297,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f297,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0,sK2),u1_struct_0(sK0)) | r3_lattices(sK0,sK1,sK6(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f296,f35])).
% 0.22/0.51  fof(f296,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0,sK2),u1_struct_0(sK0)) | r3_lattices(sK0,sK1,sK6(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f295,f32])).
% 0.22/0.51  fof(f295,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0,sK2),u1_struct_0(sK0)) | r3_lattices(sK0,sK1,sK6(sK0,sK2))),
% 0.22/0.51    inference(resolution,[],[f294,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.22/0.51  fof(f294,plain,(
% 0.22/0.51    r1_lattices(sK0,sK1,sK6(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f293,f31])).
% 0.22/0.51  fof(f293,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,sK1,sK6(sK0,sK2))),
% 0.22/0.51    inference(resolution,[],[f269,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    r2_hidden(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f269,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,sK6(sK0,X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f268,f156])).
% 0.22/0.51  fof(f268,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r1_lattices(sK0,X1,sK6(sK0,X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f267,f35])).
% 0.22/0.51  fof(f267,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r1_lattices(sK0,X1,sK6(sK0,X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f258,f32])).
% 0.22/0.51  fof(f258,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK6(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r1_lattices(sK0,X1,sK6(sK0,X0))) )),
% 0.22/0.51    inference(resolution,[],[f158,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X3,X1) | ~r4_lattice3(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 0.22/0.51  fof(f850,plain,(
% 0.22/0.51    ~r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))),
% 0.22/0.51    inference(resolution,[],[f838,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f838,plain,(
% 0.22/0.51    r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f837,f33])).
% 0.22/0.51  fof(f837,plain,(
% 0.22/0.51    r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f836,f32])).
% 0.22/0.51  fof(f836,plain,(
% 0.22/0.51    r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f835,f35])).
% 0.22/0.51  fof(f835,plain,(
% 0.22/0.51    r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f834,f38])).
% 0.22/0.51  fof(f834,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f833,f33])).
% 0.22/0.51  fof(f833,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f832,f32])).
% 0.22/0.51  fof(f832,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f831,f35])).
% 0.22/0.51  fof(f831,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f830,f40])).
% 0.22/0.51  fof(f830,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f829,f33])).
% 0.22/0.51  fof(f829,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f828,f32])).
% 0.22/0.51  fof(f828,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f827,f35])).
% 0.22/0.51  fof(f827,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f826,f41])).
% 0.22/0.51  fof(f826,plain,(
% 0.22/0.51    ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f825,f35])).
% 0.22/0.51  fof(f825,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f821,f32])).
% 0.22/0.51  fof(f821,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f819,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 0.22/0.51  fof(f819,plain,(
% 0.22/0.51    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~v6_lattices(sK0) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f818,f31])).
% 0.22/0.51  fof(f818,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f817,f35])).
% 0.22/0.51  fof(f817,plain,(
% 0.22/0.51    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f813,f32])).
% 0.22/0.51  fof(f813,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(resolution,[],[f812,f67])).
% 0.22/0.51  % (22190)Refutation not found, incomplete strategy% (22190)------------------------------
% 0.22/0.51  % (22190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22190)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22190)Memory used [KB]: 10618
% 0.22/0.51  % (22190)Time elapsed: 0.100 s
% 0.22/0.51  % (22190)------------------------------
% 0.22/0.51  % (22190)------------------------------
% 0.22/0.51  fof(f812,plain,(
% 0.22/0.51    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f811,f35])).
% 0.22/0.51  fof(f811,plain,(
% 0.22/0.51    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f807,f32])).
% 0.22/0.51  fof(f807,plain,(
% 0.22/0.51    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.22/0.51    inference(resolution,[],[f806,f66])).
% 0.22/0.51  fof(f806,plain,(
% 0.22/0.51    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f805,f32])).
% 0.22/0.51  fof(f805,plain,(
% 0.22/0.51    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f804,f31])).
% 0.22/0.51  fof(f804,plain,(
% 0.22/0.51    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f801,f35])).
% 0.22/0.51  fof(f801,plain,(
% 0.22/0.51    ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f205,f279])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    ( ! [X0] : (r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f278,f35])).
% 0.22/0.51  fof(f278,plain,(
% 0.22/0.51    ( ! [X0] : (r3_lattice3(sK0,k16_lattice3(sK0,X0),X0) | ~l3_lattices(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f274,f32])).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    ( ! [X0] : (r3_lattice3(sK0,k16_lattice3(sK0,X0),X0) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f161,f66])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ( ! [X16] : (~m1_subset_1(k16_lattice3(sK0,X16),u1_struct_0(sK0)) | r3_lattice3(sK0,k16_lattice3(sK0,X16),X16)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f160,f35])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    ( ! [X16] : (~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X16),u1_struct_0(sK0)) | r3_lattice3(sK0,k16_lattice3(sK0,X16),X16)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f159,f33])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    ( ! [X16] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X16),u1_struct_0(sK0)) | r3_lattice3(sK0,k16_lattice3(sK0,X16),X16)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f131,f32])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ( ! [X16] : (v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X16),u1_struct_0(sK0)) | r3_lattice3(sK0,k16_lattice3(sK0,X16),X16)) )),
% 0.22/0.51    inference(resolution,[],[f34,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X2,X0] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | r3_lattice3(X0,k16_lattice3(X0,X2),X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~r3_lattice3(X2,X3,sK2) | ~l3_lattices(X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_subset_1(sK1,u1_struct_0(X2)) | r1_lattices(X2,X3,sK1) | v2_struct_0(X2)) )),
% 0.22/0.51    inference(resolution,[],[f30,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X1,X3) | ~r3_lattice3(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (22202)------------------------------
% 0.22/0.51  % (22202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22202)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (22202)Memory used [KB]: 1918
% 0.22/0.51  % (22202)Time elapsed: 0.087 s
% 0.22/0.51  % (22202)------------------------------
% 0.22/0.51  % (22202)------------------------------
% 0.22/0.51  % (22188)Success in time 0.151 s
%------------------------------------------------------------------------------
