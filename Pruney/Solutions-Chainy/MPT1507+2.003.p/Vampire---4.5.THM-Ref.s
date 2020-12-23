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
% DateTime   : Thu Dec  3 13:15:42 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 732 expanded)
%              Number of leaves         :   14 ( 265 expanded)
%              Depth                    :   39
%              Number of atoms          :  594 (5224 expanded)
%              Number of equality atoms :   46 ( 673 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(subsumption_resolution,[],[f148,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK2 != k15_lattice3(sK1,sK3)
    & r4_lattice3(sK1,sK2,sK3)
    & r2_hidden(sK2,sK3)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v4_lattice3(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k15_lattice3(X0,X2) != X1
                & r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(sK1,X2) != X1
              & r4_lattice3(sK1,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v4_lattice3(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k15_lattice3(sK1,X2) != X1
            & r4_lattice3(sK1,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( ? [X2] :
          ( k15_lattice3(sK1,X2) != sK2
          & r4_lattice3(sK1,sK2,X2)
          & r2_hidden(sK2,X2) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( k15_lattice3(sK1,X2) != sK2
        & r4_lattice3(sK1,sK2,X2)
        & r2_hidden(sK2,X2) )
   => ( sK2 != k15_lattice3(sK1,sK3)
      & r4_lattice3(sK1,sK2,sK3)
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(X0,X2) != X1
              & r4_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(X0,X2) != X1
              & r4_lattice3(X0,X1,X2)
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
                ( ( r4_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k15_lattice3(X0,X2) = X1 ) ) ) ),
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
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).

fof(f148,plain,(
    v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f147,f46])).

fof(f46,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f147,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f146,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f146,plain,(
    ~ m1_subset_1(k15_lattice3(sK1,sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f145,f50])).

fof(f50,plain,(
    sK2 != k15_lattice3(sK1,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f145,plain,
    ( ~ m1_subset_1(k15_lattice3(sK1,sK3),u1_struct_0(sK1))
    | sK2 = k15_lattice3(sK1,sK3) ),
    inference(subsumption_resolution,[],[f144,f48])).

fof(f48,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f144,plain,
    ( ~ m1_subset_1(k15_lattice3(sK1,sK3),u1_struct_0(sK1))
    | ~ r2_hidden(sK2,sK3)
    | sK2 = k15_lattice3(sK1,sK3) ),
    inference(resolution,[],[f140,f95])).

fof(f95,plain,(
    r3_lattices(sK1,k15_lattice3(sK1,sK3),sK2) ),
    inference(subsumption_resolution,[],[f92,f47])).

fof(f47,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r3_lattices(sK1,k15_lattice3(sK1,sK3),sK2) ),
    inference(resolution,[],[f91,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,a_2_2_lattice3(sK1,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r3_lattices(sK1,k15_lattice3(sK1,X0),X1) ) ),
    inference(superposition,[],[f84,f80])).

fof(f80,plain,(
    ! [X0] : k15_lattice3(sK1,X0) = k16_lattice3(sK1,a_2_2_lattice3(sK1,X0)) ),
    inference(subsumption_resolution,[],[f79,f43])).

fof(f79,plain,(
    ! [X0] :
      ( k15_lattice3(sK1,X0) = k16_lattice3(sK1,a_2_2_lattice3(sK1,X0))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f78,f44])).

fof(f44,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X0] :
      ( k15_lattice3(sK1,X0) = k16_lattice3(sK1,a_2_2_lattice3(sK1,X0))
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f77,f46])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK1)
      | k15_lattice3(sK1,X0) = k16_lattice3(sK1,a_2_2_lattice3(sK1,X0))
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f59,f45])).

fof(f45,plain,(
    v4_lattice3(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
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
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

fof(f84,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK1,k16_lattice3(sK1,X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f83,f43])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattices(sK1,k16_lattice3(sK1,X1),X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f82,f44])).

% (10540)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattices(sK1,k16_lattice3(sK1,X1),X0)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f81,f46])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | r3_lattices(sK1,k16_lattice3(sK1,X1),X0)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f61,f45])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

fof(f91,plain,(
    r2_hidden(sK2,a_2_2_lattice3(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f90,f47])).

fof(f90,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,a_2_2_lattice3(sK1,sK3)) ),
    inference(resolution,[],[f89,f49])).

fof(f49,plain,(
    r4_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r2_hidden(X0,a_2_2_lattice3(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f88,f43])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r2_hidden(X0,a_2_2_lattice3(sK1,X1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f87,f44])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r2_hidden(X0,a_2_2_lattice3(sK1,X1))
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f86,f46])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | r2_hidden(X0,a_2_2_lattice3(sK1,X1))
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f69,f45])).

fof(f69,plain,(
    ! [X2,X3,X1] :
      ( ~ v4_lattice3(X1)
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK4(X0,X1,X2),X2)
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK4(X0,X1,X2),X2)
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r4_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r4_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f140,plain,(
    ! [X0] :
      ( ~ r3_lattices(sK1,k15_lattice3(sK1,X0),sK2)
      | ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | ~ r2_hidden(sK2,X0)
      | sK2 = k15_lattice3(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f139,f47])).

fof(f139,plain,(
    ! [X0] :
      ( sK2 = k15_lattice3(sK1,X0)
      | ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | ~ r2_hidden(sK2,X0)
      | ~ r3_lattices(sK1,k15_lattice3(sK1,X0),sK2)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f138,f115])).

fof(f115,plain,(
    ! [X2,X1] :
      ( r1_lattices(sK1,k15_lattice3(sK1,X2),X1)
      | ~ r3_lattices(sK1,k15_lattice3(sK1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f114,f43])).

fof(f114,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r3_lattices(sK1,k15_lattice3(sK1,X2),X1)
      | r1_lattices(sK1,k15_lattice3(sK1,X2),X1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f112,f46])).

fof(f112,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r3_lattices(sK1,k15_lattice3(sK1,X2),X1)
      | r1_lattices(sK1,k15_lattice3(sK1,X2),X1)
      | ~ l3_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f110,f62])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r3_lattices(sK1,X0,X1)
      | r1_lattices(sK1,X0,X1) ) ),
    inference(subsumption_resolution,[],[f109,f43])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_lattices(sK1,X0,X1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f108,f75])).

% (10545)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f75,plain,(
    v6_lattices(sK1) ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f72,plain,(
    sP0(sK1) ),
    inference(subsumption_resolution,[],[f71,f46])).

fof(f71,plain,
    ( sP0(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f70,f43])).

fof(f70,plain,
    ( sP0(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1) ),
    inference(resolution,[],[f57,f44])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | sP0(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f18,f31])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
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
          & v4_lattices(X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_lattices(sK1,X0,X1)
      | ~ v6_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f107,f74])).

fof(f74,plain,(
    v8_lattices(sK1) ),
    inference(resolution,[],[f72,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_lattices(sK1,X0,X1)
      | ~ v8_lattices(sK1)
      | ~ v6_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f106,f46])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | r1_lattices(sK1,X0,X1)
      | ~ v8_lattices(sK1)
      | ~ v6_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f63,f73])).

fof(f73,plain,(
    v9_lattices(sK1) ),
    inference(resolution,[],[f72,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f138,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK1,k15_lattice3(sK1,X0),sK2)
      | sK2 = k15_lattice3(sK1,X0)
      | ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f137,f46])).

fof(f137,plain,(
    ! [X0] :
      ( sK2 = k15_lattice3(sK1,X0)
      | ~ r1_lattices(sK1,k15_lattice3(sK1,X0),sK2)
      | ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | ~ r2_hidden(sK2,X0)
      | ~ l3_lattices(sK1) ) ),
    inference(resolution,[],[f132,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f132,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK1)
      | sK2 = k15_lattice3(sK1,X0)
      | ~ r1_lattices(sK1,k15_lattice3(sK1,X0),sK2)
      | ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f131,f43])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | sK2 = k15_lattice3(sK1,X0)
      | ~ r1_lattices(sK1,k15_lattice3(sK1,X0),sK2)
      | ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | ~ l2_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f130,f76])).

fof(f76,plain,(
    v4_lattices(sK1) ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f130,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | sK2 = k15_lattice3(sK1,X0)
      | ~ r1_lattices(sK1,k15_lattice3(sK1,X0),sK2)
      | ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | ~ l2_lattices(sK1)
      | ~ v4_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f129,f47])).

fof(f129,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | sK2 = k15_lattice3(sK1,X0)
      | ~ r1_lattices(sK1,k15_lattice3(sK1,X0),sK2)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | ~ l2_lattices(sK1)
      | ~ v4_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f128,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(f128,plain,(
    ! [X0] :
      ( r1_lattices(sK1,sK2,k15_lattice3(sK1,X0))
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f127,f43])).

fof(f127,plain,(
    ! [X0] :
      ( r1_lattices(sK1,sK2,k15_lattice3(sK1,X0))
      | ~ r2_hidden(sK2,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f126,f46])).

fof(f126,plain,(
    ! [X0] :
      ( r1_lattices(sK1,sK2,k15_lattice3(sK1,X0))
      | ~ r2_hidden(sK2,X0)
      | ~ l3_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f125,f62])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0))
      | ~ r2_hidden(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f124,f43])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0))
      | ~ r2_hidden(sK2,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f123,f44])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0))
      | ~ r2_hidden(sK2,X0)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f122,f45])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0))
      | ~ r2_hidden(sK2,X0)
      | ~ v4_lattice3(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f121,f46])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0))
      | ~ r2_hidden(sK2,X0)
      | ~ l3_lattices(sK1)
      | ~ v4_lattice3(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f120,f47])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1))
      | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0))
      | ~ r2_hidden(sK2,X0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | ~ v4_lattice3(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f111,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r3_lattices(sK1,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_lattices(sK1,sK2,X0) ) ),
    inference(resolution,[],[f110,f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:53:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (10535)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (10549)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (10552)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (10536)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (10542)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (10533)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (10544)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.23/0.52  % (10547)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.23/0.52  % (10535)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % (10551)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.23/0.53  % (10537)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.23/0.53  % (10534)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.23/0.53  % (10553)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.23/0.53  % (10533)Refutation not found, incomplete strategy% (10533)------------------------------
% 1.23/0.53  % (10533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (10533)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (10533)Memory used [KB]: 10618
% 1.23/0.53  % (10539)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.23/0.53  % (10543)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.23/0.53  % (10533)Time elapsed: 0.072 s
% 1.23/0.53  % (10533)------------------------------
% 1.23/0.53  % (10533)------------------------------
% 1.23/0.53  % SZS output start Proof for theBenchmark
% 1.23/0.53  fof(f149,plain,(
% 1.23/0.53    $false),
% 1.23/0.53    inference(subsumption_resolution,[],[f148,f43])).
% 1.23/0.53  fof(f43,plain,(
% 1.23/0.53    ~v2_struct_0(sK1)),
% 1.23/0.53    inference(cnf_transformation,[],[f36])).
% 1.23/0.53  fof(f36,plain,(
% 1.23/0.53    ((sK2 != k15_lattice3(sK1,sK3) & r4_lattice3(sK1,sK2,sK3) & r2_hidden(sK2,sK3)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l3_lattices(sK1) & v4_lattice3(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)),
% 1.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f35,f34,f33])).
% 1.23/0.53  fof(f33,plain,(
% 1.23/0.53    ? [X0] : (? [X1] : (? [X2] : (k15_lattice3(X0,X2) != X1 & r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k15_lattice3(sK1,X2) != X1 & r4_lattice3(sK1,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK1))) & l3_lattices(sK1) & v4_lattice3(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f34,plain,(
% 1.23/0.53    ? [X1] : (? [X2] : (k15_lattice3(sK1,X2) != X1 & r4_lattice3(sK1,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK1))) => (? [X2] : (k15_lattice3(sK1,X2) != sK2 & r4_lattice3(sK1,sK2,X2) & r2_hidden(sK2,X2)) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f35,plain,(
% 1.23/0.53    ? [X2] : (k15_lattice3(sK1,X2) != sK2 & r4_lattice3(sK1,sK2,X2) & r2_hidden(sK2,X2)) => (sK2 != k15_lattice3(sK1,sK3) & r4_lattice3(sK1,sK2,sK3) & r2_hidden(sK2,sK3))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f15,plain,(
% 1.23/0.53    ? [X0] : (? [X1] : (? [X2] : (k15_lattice3(X0,X2) != X1 & r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.23/0.53    inference(flattening,[],[f14])).
% 1.23/0.53  fof(f14,plain,(
% 1.23/0.53    ? [X0] : (? [X1] : (? [X2] : (k15_lattice3(X0,X2) != X1 & (r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.23/0.53    inference(ennf_transformation,[],[f10])).
% 1.23/0.53  fof(f10,negated_conjecture,(
% 1.23/0.53    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 1.23/0.53    inference(negated_conjecture,[],[f9])).
% 1.23/0.53  fof(f9,conjecture,(
% 1.23/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).
% 1.23/0.53  fof(f148,plain,(
% 1.23/0.53    v2_struct_0(sK1)),
% 1.23/0.53    inference(subsumption_resolution,[],[f147,f46])).
% 1.23/0.53  fof(f46,plain,(
% 1.23/0.53    l3_lattices(sK1)),
% 1.23/0.53    inference(cnf_transformation,[],[f36])).
% 1.23/0.53  fof(f147,plain,(
% 1.23/0.53    ~l3_lattices(sK1) | v2_struct_0(sK1)),
% 1.23/0.53    inference(resolution,[],[f146,f62])).
% 1.23/0.53  fof(f62,plain,(
% 1.23/0.53    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f26])).
% 1.23/0.53  fof(f26,plain,(
% 1.23/0.53    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.23/0.53    inference(flattening,[],[f25])).
% 1.23/0.53  fof(f25,plain,(
% 1.23/0.53    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.23/0.53    inference(ennf_transformation,[],[f5])).
% 1.23/0.53  fof(f5,axiom,(
% 1.23/0.53    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.23/0.53  fof(f146,plain,(
% 1.23/0.53    ~m1_subset_1(k15_lattice3(sK1,sK3),u1_struct_0(sK1))),
% 1.23/0.53    inference(subsumption_resolution,[],[f145,f50])).
% 1.23/0.53  fof(f50,plain,(
% 1.23/0.53    sK2 != k15_lattice3(sK1,sK3)),
% 1.23/0.53    inference(cnf_transformation,[],[f36])).
% 1.23/0.53  fof(f145,plain,(
% 1.23/0.53    ~m1_subset_1(k15_lattice3(sK1,sK3),u1_struct_0(sK1)) | sK2 = k15_lattice3(sK1,sK3)),
% 1.23/0.53    inference(subsumption_resolution,[],[f144,f48])).
% 1.23/0.53  fof(f48,plain,(
% 1.23/0.53    r2_hidden(sK2,sK3)),
% 1.23/0.53    inference(cnf_transformation,[],[f36])).
% 1.23/0.53  fof(f144,plain,(
% 1.23/0.53    ~m1_subset_1(k15_lattice3(sK1,sK3),u1_struct_0(sK1)) | ~r2_hidden(sK2,sK3) | sK2 = k15_lattice3(sK1,sK3)),
% 1.23/0.53    inference(resolution,[],[f140,f95])).
% 1.23/0.53  fof(f95,plain,(
% 1.23/0.53    r3_lattices(sK1,k15_lattice3(sK1,sK3),sK2)),
% 1.23/0.53    inference(subsumption_resolution,[],[f92,f47])).
% 1.23/0.53  fof(f47,plain,(
% 1.23/0.53    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.23/0.53    inference(cnf_transformation,[],[f36])).
% 1.23/0.53  fof(f92,plain,(
% 1.23/0.53    ~m1_subset_1(sK2,u1_struct_0(sK1)) | r3_lattices(sK1,k15_lattice3(sK1,sK3),sK2)),
% 1.23/0.53    inference(resolution,[],[f91,f85])).
% 1.23/0.53  fof(f85,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r2_hidden(X1,a_2_2_lattice3(sK1,X0)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | r3_lattices(sK1,k15_lattice3(sK1,X0),X1)) )),
% 1.23/0.53    inference(superposition,[],[f84,f80])).
% 1.23/0.53  fof(f80,plain,(
% 1.23/0.53    ( ! [X0] : (k15_lattice3(sK1,X0) = k16_lattice3(sK1,a_2_2_lattice3(sK1,X0))) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f79,f43])).
% 1.23/0.53  fof(f79,plain,(
% 1.23/0.53    ( ! [X0] : (k15_lattice3(sK1,X0) = k16_lattice3(sK1,a_2_2_lattice3(sK1,X0)) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f78,f44])).
% 1.23/0.53  fof(f44,plain,(
% 1.23/0.53    v10_lattices(sK1)),
% 1.23/0.53    inference(cnf_transformation,[],[f36])).
% 1.23/0.53  fof(f78,plain,(
% 1.23/0.53    ( ! [X0] : (k15_lattice3(sK1,X0) = k16_lattice3(sK1,a_2_2_lattice3(sK1,X0)) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f77,f46])).
% 1.23/0.53  fof(f77,plain,(
% 1.23/0.53    ( ! [X0] : (~l3_lattices(sK1) | k15_lattice3(sK1,X0) = k16_lattice3(sK1,a_2_2_lattice3(sK1,X0)) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(resolution,[],[f59,f45])).
% 1.23/0.53  fof(f45,plain,(
% 1.23/0.53    v4_lattice3(sK1)),
% 1.23/0.53    inference(cnf_transformation,[],[f36])).
% 1.23/0.53  fof(f59,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f22])).
% 1.23/0.53  fof(f22,plain,(
% 1.23/0.53    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.23/0.53    inference(flattening,[],[f21])).
% 1.23/0.53  fof(f21,plain,(
% 1.23/0.53    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.23/0.53    inference(ennf_transformation,[],[f7])).
% 1.23/0.53  fof(f7,axiom,(
% 1.23/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).
% 1.23/0.53  fof(f84,plain,(
% 1.23/0.53    ( ! [X0,X1] : (r3_lattices(sK1,k16_lattice3(sK1,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r2_hidden(X0,X1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f83,f43])).
% 1.23/0.53  fof(f83,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r3_lattices(sK1,k16_lattice3(sK1,X1),X0) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f82,f44])).
% 1.23/0.53  % (10540)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.23/0.53  fof(f82,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r3_lattices(sK1,k16_lattice3(sK1,X1),X0) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f81,f46])).
% 1.23/0.53  fof(f81,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l3_lattices(sK1) | r3_lattices(sK1,k16_lattice3(sK1,X1),X0) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(resolution,[],[f61,f45])).
% 1.23/0.53  fof(f61,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f24])).
% 1.23/0.53  fof(f24,plain,(
% 1.23/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.23/0.53    inference(flattening,[],[f23])).
% 1.23/0.53  fof(f23,plain,(
% 1.23/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.23/0.53    inference(ennf_transformation,[],[f8])).
% 1.23/0.53  fof(f8,axiom,(
% 1.23/0.53    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).
% 1.23/0.53  fof(f91,plain,(
% 1.23/0.53    r2_hidden(sK2,a_2_2_lattice3(sK1,sK3))),
% 1.23/0.53    inference(subsumption_resolution,[],[f90,f47])).
% 1.23/0.53  fof(f90,plain,(
% 1.23/0.53    ~m1_subset_1(sK2,u1_struct_0(sK1)) | r2_hidden(sK2,a_2_2_lattice3(sK1,sK3))),
% 1.23/0.53    inference(resolution,[],[f89,f49])).
% 1.23/0.53  fof(f49,plain,(
% 1.23/0.53    r4_lattice3(sK1,sK2,sK3)),
% 1.23/0.53    inference(cnf_transformation,[],[f36])).
% 1.23/0.53  fof(f89,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r4_lattice3(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r2_hidden(X0,a_2_2_lattice3(sK1,X1))) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f88,f43])).
% 1.23/0.53  fof(f88,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r4_lattice3(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r2_hidden(X0,a_2_2_lattice3(sK1,X1)) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f87,f44])).
% 1.23/0.53  fof(f87,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r4_lattice3(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r2_hidden(X0,a_2_2_lattice3(sK1,X1)) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f86,f46])).
% 1.23/0.53  fof(f86,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r4_lattice3(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l3_lattices(sK1) | r2_hidden(X0,a_2_2_lattice3(sK1,X1)) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(resolution,[],[f69,f45])).
% 1.23/0.53  fof(f69,plain,(
% 1.23/0.53    ( ! [X2,X3,X1] : (~v4_lattice3(X1) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.23/0.53    inference(equality_resolution,[],[f68])).
% 1.23/0.53  fof(f68,plain,(
% 1.23/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f42])).
% 1.23/0.53  fof(f42,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK4(X0,X1,X2),X2) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.23/0.53  fof(f41,plain,(
% 1.23/0.53    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK4(X0,X1,X2),X2) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f40,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.23/0.53    inference(rectify,[],[f39])).
% 1.23/0.53  fof(f39,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.23/0.53    inference(nnf_transformation,[],[f30])).
% 1.23/0.53  fof(f30,plain,(
% 1.23/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.23/0.53    inference(flattening,[],[f29])).
% 1.23/0.53  fof(f29,plain,(
% 1.23/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.23/0.53    inference(ennf_transformation,[],[f6])).
% 1.23/0.53  fof(f6,axiom,(
% 1.23/0.53    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 1.23/0.53  fof(f140,plain,(
% 1.23/0.53    ( ! [X0] : (~r3_lattices(sK1,k15_lattice3(sK1,X0),sK2) | ~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | ~r2_hidden(sK2,X0) | sK2 = k15_lattice3(sK1,X0)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f139,f47])).
% 1.23/0.53  fof(f139,plain,(
% 1.23/0.53    ( ! [X0] : (sK2 = k15_lattice3(sK1,X0) | ~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | ~r2_hidden(sK2,X0) | ~r3_lattices(sK1,k15_lattice3(sK1,X0),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK1))) )),
% 1.23/0.53    inference(resolution,[],[f138,f115])).
% 1.23/0.53  fof(f115,plain,(
% 1.23/0.53    ( ! [X2,X1] : (r1_lattices(sK1,k15_lattice3(sK1,X2),X1) | ~r3_lattices(sK1,k15_lattice3(sK1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(sK1))) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f114,f43])).
% 1.23/0.53  fof(f114,plain,(
% 1.23/0.53    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | ~r3_lattices(sK1,k15_lattice3(sK1,X2),X1) | r1_lattices(sK1,k15_lattice3(sK1,X2),X1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f112,f46])).
% 1.23/0.53  fof(f112,plain,(
% 1.23/0.53    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | ~r3_lattices(sK1,k15_lattice3(sK1,X2),X1) | r1_lattices(sK1,k15_lattice3(sK1,X2),X1) | ~l3_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(resolution,[],[f110,f62])).
% 1.23/0.53  fof(f110,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r3_lattices(sK1,X0,X1) | r1_lattices(sK1,X0,X1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f109,f43])).
% 1.23/0.53  fof(f109,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r3_lattices(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_lattices(sK1,X0,X1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f108,f75])).
% 1.23/0.53  % (10545)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.23/0.53  fof(f75,plain,(
% 1.23/0.53    v6_lattices(sK1)),
% 1.23/0.53    inference(resolution,[],[f72,f54])).
% 1.23/0.53  fof(f54,plain,(
% 1.23/0.53    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f37])).
% 1.23/0.53  fof(f37,plain,(
% 1.23/0.53    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 1.23/0.53    inference(nnf_transformation,[],[f31])).
% 1.23/0.53  fof(f31,plain,(
% 1.23/0.53    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 1.23/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.23/0.53  fof(f72,plain,(
% 1.23/0.53    sP0(sK1)),
% 1.23/0.53    inference(subsumption_resolution,[],[f71,f46])).
% 1.23/0.53  fof(f71,plain,(
% 1.23/0.53    sP0(sK1) | ~l3_lattices(sK1)),
% 1.23/0.53    inference(subsumption_resolution,[],[f70,f43])).
% 1.23/0.53  fof(f70,plain,(
% 1.23/0.53    sP0(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK1)),
% 1.23/0.53    inference(resolution,[],[f57,f44])).
% 1.23/0.53  fof(f57,plain,(
% 1.23/0.53    ( ! [X0] : (~v10_lattices(X0) | sP0(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f32])).
% 1.23/0.53  fof(f32,plain,(
% 1.23/0.53    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.23/0.53    inference(definition_folding,[],[f18,f31])).
% 1.23/0.53  fof(f18,plain,(
% 1.23/0.53    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.23/0.53    inference(flattening,[],[f17])).
% 1.23/0.53  fof(f17,plain,(
% 1.23/0.53    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.23/0.53    inference(ennf_transformation,[],[f13])).
% 1.23/0.53  fof(f13,plain,(
% 1.23/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.23/0.53    inference(pure_predicate_removal,[],[f12])).
% 1.23/0.53  fof(f12,plain,(
% 1.23/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.23/0.53    inference(pure_predicate_removal,[],[f1])).
% 1.23/0.53  fof(f1,axiom,(
% 1.23/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 1.23/0.53  fof(f108,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r3_lattices(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_lattices(sK1,X0,X1) | ~v6_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f107,f74])).
% 1.23/0.53  fof(f74,plain,(
% 1.23/0.53    v8_lattices(sK1)),
% 1.23/0.53    inference(resolution,[],[f72,f55])).
% 1.23/0.53  fof(f55,plain,(
% 1.23/0.53    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f37])).
% 1.23/0.53  fof(f107,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r3_lattices(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_lattices(sK1,X0,X1) | ~v8_lattices(sK1) | ~v6_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f106,f46])).
% 1.23/0.53  fof(f106,plain,(
% 1.23/0.53    ( ! [X0,X1] : (~r3_lattices(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~l3_lattices(sK1) | r1_lattices(sK1,X0,X1) | ~v8_lattices(sK1) | ~v6_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.53    inference(resolution,[],[f63,f73])).
% 1.23/0.53  fof(f73,plain,(
% 1.23/0.53    v9_lattices(sK1)),
% 1.23/0.53    inference(resolution,[],[f72,f56])).
% 1.23/0.53  fof(f56,plain,(
% 1.23/0.53    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f37])).
% 1.23/0.53  fof(f63,plain,(
% 1.23/0.53    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f38])).
% 1.23/0.53  fof(f38,plain,(
% 1.23/0.53    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.23/0.53    inference(nnf_transformation,[],[f28])).
% 1.23/0.53  fof(f28,plain,(
% 1.23/0.53    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.23/0.53    inference(flattening,[],[f27])).
% 1.23/0.53  fof(f27,plain,(
% 1.23/0.53    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.23/0.53    inference(ennf_transformation,[],[f3])).
% 1.23/0.53  fof(f3,axiom,(
% 1.23/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.23/0.53  fof(f138,plain,(
% 1.23/0.53    ( ! [X0] : (~r1_lattices(sK1,k15_lattice3(sK1,X0),sK2) | sK2 = k15_lattice3(sK1,X0) | ~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | ~r2_hidden(sK2,X0)) )),
% 1.23/0.53    inference(subsumption_resolution,[],[f137,f46])).
% 1.23/0.53  fof(f137,plain,(
% 1.23/0.53    ( ! [X0] : (sK2 = k15_lattice3(sK1,X0) | ~r1_lattices(sK1,k15_lattice3(sK1,X0),sK2) | ~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | ~r2_hidden(sK2,X0) | ~l3_lattices(sK1)) )),
% 1.23/0.53    inference(resolution,[],[f132,f51])).
% 1.23/0.53  fof(f51,plain,(
% 1.23/0.53    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f16])).
% 1.23/0.53  fof(f16,plain,(
% 1.23/0.53    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 1.23/0.53    inference(ennf_transformation,[],[f11])).
% 1.23/0.54  fof(f11,plain,(
% 1.23/0.54    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 1.23/0.54    inference(pure_predicate_removal,[],[f2])).
% 1.23/0.54  fof(f2,axiom,(
% 1.23/0.54    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.23/0.54  fof(f132,plain,(
% 1.23/0.54    ( ! [X0] : (~l2_lattices(sK1) | sK2 = k15_lattice3(sK1,X0) | ~r1_lattices(sK1,k15_lattice3(sK1,X0),sK2) | ~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | ~r2_hidden(sK2,X0)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f131,f43])).
% 1.23/0.54  fof(f131,plain,(
% 1.23/0.54    ( ! [X0] : (~r2_hidden(sK2,X0) | sK2 = k15_lattice3(sK1,X0) | ~r1_lattices(sK1,k15_lattice3(sK1,X0),sK2) | ~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | ~l2_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f130,f76])).
% 1.23/0.54  fof(f76,plain,(
% 1.23/0.54    v4_lattices(sK1)),
% 1.23/0.54    inference(resolution,[],[f72,f53])).
% 1.23/0.54  fof(f53,plain,(
% 1.23/0.54    ( ! [X0] : (~sP0(X0) | v4_lattices(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f37])).
% 1.23/0.54  fof(f130,plain,(
% 1.23/0.54    ( ! [X0] : (~r2_hidden(sK2,X0) | sK2 = k15_lattice3(sK1,X0) | ~r1_lattices(sK1,k15_lattice3(sK1,X0),sK2) | ~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | ~l2_lattices(sK1) | ~v4_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f129,f47])).
% 1.23/0.54  fof(f129,plain,(
% 1.23/0.54    ( ! [X0] : (~r2_hidden(sK2,X0) | sK2 = k15_lattice3(sK1,X0) | ~r1_lattices(sK1,k15_lattice3(sK1,X0),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | ~l2_lattices(sK1) | ~v4_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.54    inference(resolution,[],[f128,f58])).
% 1.23/0.54  fof(f58,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X2,X1) | X1 = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f20])).
% 1.23/0.54  fof(f20,plain,(
% 1.23/0.54    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.23/0.54    inference(flattening,[],[f19])).
% 1.23/0.54  fof(f19,plain,(
% 1.23/0.54    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.23/0.54    inference(ennf_transformation,[],[f4])).
% 1.23/0.54  fof(f4,axiom,(
% 1.23/0.54    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 1.23/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).
% 1.23/0.54  fof(f128,plain,(
% 1.23/0.54    ( ! [X0] : (r1_lattices(sK1,sK2,k15_lattice3(sK1,X0)) | ~r2_hidden(sK2,X0)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f127,f43])).
% 1.23/0.54  fof(f127,plain,(
% 1.23/0.54    ( ! [X0] : (r1_lattices(sK1,sK2,k15_lattice3(sK1,X0)) | ~r2_hidden(sK2,X0) | v2_struct_0(sK1)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f126,f46])).
% 1.23/0.54  fof(f126,plain,(
% 1.23/0.54    ( ! [X0] : (r1_lattices(sK1,sK2,k15_lattice3(sK1,X0)) | ~r2_hidden(sK2,X0) | ~l3_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.54    inference(resolution,[],[f125,f62])).
% 1.23/0.54  fof(f125,plain,(
% 1.23/0.54    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0)) | ~r2_hidden(sK2,X0)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f124,f43])).
% 1.23/0.54  fof(f124,plain,(
% 1.23/0.54    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0)) | ~r2_hidden(sK2,X0) | v2_struct_0(sK1)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f123,f44])).
% 1.23/0.54  fof(f123,plain,(
% 1.23/0.54    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0)) | ~r2_hidden(sK2,X0) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f122,f45])).
% 1.23/0.54  fof(f122,plain,(
% 1.23/0.54    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0)) | ~r2_hidden(sK2,X0) | ~v4_lattice3(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f121,f46])).
% 1.23/0.54  fof(f121,plain,(
% 1.23/0.54    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0)) | ~r2_hidden(sK2,X0) | ~l3_lattices(sK1) | ~v4_lattice3(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f120,f47])).
% 1.23/0.54  fof(f120,plain,(
% 1.23/0.54    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK1,X0),u1_struct_0(sK1)) | r1_lattices(sK1,sK2,k15_lattice3(sK1,X0)) | ~r2_hidden(sK2,X0) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l3_lattices(sK1) | ~v4_lattice3(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 1.23/0.54    inference(resolution,[],[f111,f60])).
% 1.23/0.54  fof(f60,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f24])).
% 1.23/0.54  fof(f111,plain,(
% 1.23/0.54    ( ! [X0] : (~r3_lattices(sK1,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_lattices(sK1,sK2,X0)) )),
% 1.23/0.54    inference(resolution,[],[f110,f47])).
% 1.23/0.54  % SZS output end Proof for theBenchmark
% 1.23/0.54  % (10535)------------------------------
% 1.23/0.54  % (10535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (10535)Termination reason: Refutation
% 1.23/0.54  
% 1.23/0.54  % (10535)Memory used [KB]: 6268
% 1.23/0.54  % (10535)Time elapsed: 0.105 s
% 1.23/0.54  % (10535)------------------------------
% 1.23/0.54  % (10535)------------------------------
% 1.23/0.54  % (10531)Success in time 0.171 s
%------------------------------------------------------------------------------
