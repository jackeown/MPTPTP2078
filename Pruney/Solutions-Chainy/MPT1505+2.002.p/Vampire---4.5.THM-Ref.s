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
% DateTime   : Thu Dec  3 13:15:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  153 (1593 expanded)
%              Number of leaves         :   16 ( 547 expanded)
%              Depth                    :   48
%              Number of atoms          :  844 (11830 expanded)
%              Number of equality atoms :   42 ( 176 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(subsumption_resolution,[],[f358,f55])).

fof(f55,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
      | ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) )
    & r2_hidden(sK1,sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,k16_lattice3(X0,X2),X1)
                  | ~ r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,X2),X1)
                | ~ r3_lattices(sK0,X1,k15_lattice3(sK0,X2)) )
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,X2),X1)
              | ~ r3_lattices(sK0,X1,k15_lattice3(sK0,X2)) )
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,X2),sK1)
            | ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,X2)) )
          & r2_hidden(sK1,X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,X2),sK1)
          | ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,X2)) )
        & r2_hidden(sK1,X2) )
   => ( ( ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
        | ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) )
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(f358,plain,(
    ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f357,f155])).

fof(f155,plain,(
    ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f154,f56])).

fof(f56,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f154,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f150,f55])).

fof(f150,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,sK2)
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(resolution,[],[f149,f57])).

fof(f57,plain,
    ( ~ r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | ~ r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f149,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f148,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f148,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f146,f54])).

fof(f54,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f146,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f141,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f141,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
      | r3_lattices(sK0,X2,k15_lattice3(sK0,X3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r3_lattices(sK0,X2,k15_lattice3(sK0,X3))
      | ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f138,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f124,f51])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f122,f54])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f115,f79])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1)) ) ),
    inference(resolution,[],[f114,f111])).

fof(f111,plain,(
    ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) ),
    inference(subsumption_resolution,[],[f110,f51])).

fof(f110,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f52])).

fof(f52,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f109,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f108,f54])).

fof(f108,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f107,f53])).

fof(f53,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f89,f79])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK3(X0,X1,X2))
                & r4_lattice3(X0,sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK3(X0,X1,X2))
        & r4_lattice3(X0,sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(sK0,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X2) ) ),
    inference(subsumption_resolution,[],[f113,f51])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f75,f54])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X4,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

% (22357)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
                  & r2_hidden(sK5(X0,X1,X2),X2)
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f137,f51])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f136,f54])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f135,f52])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f134,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f133,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f81,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f26])).

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

fof(f357,plain,
    ( r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f356,f98])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f97,f51])).

fof(f97,plain,(
    ! [X0] :
      ( m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f96,f54])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f79,f95])).

fof(f95,plain,(
    ! [X0] : k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X0)) ),
    inference(subsumption_resolution,[],[f94,f54])).

fof(f94,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X0)) ) ),
    inference(resolution,[],[f70,f51])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

fof(f356,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f354,f138])).

fof(f354,plain,(
    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f353,f95])).

fof(f353,plain,(
    r1_lattices(sK0,k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f351,f55])).

fof(f351,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)),sK1) ),
    inference(resolution,[],[f350,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) ) ),
    inference(subsumption_resolution,[],[f175,f51])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f174,f52])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f173,f54])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f172,f53])).

fof(f172,plain,(
    ! [X4,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f90,f79])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f350,plain,(
    r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f349,f51])).

fof(f349,plain,
    ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f348,f54])).

fof(f348,plain,
    ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f345,f55])).

fof(f345,plain,
    ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f342,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f342,plain,
    ( r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1)
    | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f339,f55])).

fof(f339,plain,
    ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1) ),
    inference(resolution,[],[f338,f56])).

fof(f338,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f318,f322])).

fof(f322,plain,
    ( m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f321,f55])).

fof(f321,plain,
    ( m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f314,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK0,X0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r4_lattice3(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK0,X0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r4_lattice3(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f77,f54])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r4_lattice3(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f314,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f313,f51])).

fof(f313,plain,
    ( m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f311,f54])).

fof(f311,plain,
    ( m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f82,f309])).

fof(f309,plain,(
    sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)) = sK6(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK0,sK2) ),
    inference(subsumption_resolution,[],[f306,f55])).

fof(f306,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)) = sK6(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK0,sK2) ),
    inference(resolution,[],[f297,f155])).

fof(f297,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k16_lattice3(sK0,X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) ) ),
    inference(subsumption_resolution,[],[f296,f98])).

fof(f296,plain,(
    ! [X0,X1] :
      ( sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))
      | r3_lattices(sK0,k16_lattice3(sK0,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,(
    ! [X0,X1] :
      ( sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))
      | r3_lattices(sK0,k16_lattice3(sK0,X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f292,f138])).

fof(f292,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k16_lattice3(sK0,X1),X0)
      | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f291,f95])).

fof(f291,plain,(
    ! [X0,X1] :
      ( sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,a_2_1_lattice3(sK0,X1)),X0) ) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,(
    ! [X0,X1] :
      ( sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,a_2_1_lattice3(sK0,X1)),X0) ) ),
    inference(resolution,[],[f287,f176])).

fof(f287,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
      | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f286,f51])).

fof(f286,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
      | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f106,f54])).

fof(f106,plain,(
    ! [X4,X5,X3] :
      ( ~ l3_lattices(X4)
      | r4_lattice3(sK0,X3,a_2_1_lattice3(X4,X5))
      | sK5(sK0,X3,a_2_1_lattice3(X4,X5)) = sK6(sK5(sK0,X3,a_2_1_lattice3(X4,X5)),X4,X5)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f104,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sK6(X0,X1,X2) = X0
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r3_lattice3(X1,sK6(X0,X1,X2),X2)
            & sK6(X0,X1,X2) = X0
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK6(X0,X1,X2),X2)
        & sK6(X0,X1,X2) = X0
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r3_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r3_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r3_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

% (22357)Refutation not found, incomplete strategy% (22357)------------------------------
% (22357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22357)Termination reason: Refutation not found, incomplete strategy

% (22357)Memory used [KB]: 10618
% (22357)Time elapsed: 0.091 s
% (22357)------------------------------
% (22357)------------------------------
fof(f318,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0)
      | ~ m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f317,f51])).

fof(f317,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0)
      | ~ m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f315,f54])).

fof(f315,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
      | ~ r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0)
      | ~ m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f312,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r3_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattices(X0,X1,X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK4(X0,X1,X2))
                  & r2_hidden(sK4(X0,X1,X2),X2)
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f312,plain,
    ( r3_lattice3(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK2)
    | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f310,f55])).

fof(f310,plain,
    ( r3_lattice3(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK2)
    | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[],[f165,f309])).

fof(f165,plain,(
    ! [X0,X1] :
      ( r3_lattice3(sK0,sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1)
      | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f164,f51])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1))
      | r3_lattice3(sK0,sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f105,f54])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X1)
      | r4_lattice3(sK0,X0,a_2_1_lattice3(X1,X2))
      | r3_lattice3(X1,sK6(sK5(sK0,X0,a_2_1_lattice3(X1,X2)),X1,X2),X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f104,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | r3_lattice3(X1,sK6(X0,X1,X2),X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:37:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22370)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (22378)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.49  % (22364)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.49  % (22378)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (22372)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f359,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f358,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    (((~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))) & r2_hidden(sK1,sK2)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f31,f30,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r3_lattices(X0,X1,k15_lattice3(X0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_lattices(sK0,k16_lattice3(sK0,X2),X1) | ~r3_lattices(sK0,X1,k15_lattice3(sK0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : ((~r3_lattices(sK0,k16_lattice3(sK0,X2),X1) | ~r3_lattices(sK0,X1,k15_lattice3(sK0,X2))) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r3_lattices(sK0,k16_lattice3(sK0,X2),sK1) | ~r3_lattices(sK0,sK1,k15_lattice3(sK0,X2))) & r2_hidden(sK1,X2)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ? [X2] : ((~r3_lattices(sK0,k16_lattice3(sK0,X2),sK1) | ~r3_lattices(sK0,sK1,k15_lattice3(sK0,X2))) & r2_hidden(sK1,X2)) => ((~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))) & r2_hidden(sK1,sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
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
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 0.22/0.51  fof(f358,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f357,f155])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f154,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    r2_hidden(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ~r2_hidden(sK1,sK2) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f150,f55])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK2) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(resolution,[],[f149,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ~r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | ~r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_lattices(sK0,X0,k15_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f148,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_lattices(sK0,X0,k15_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f146,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    l3_lattices(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_lattices(sK0,X0,k15_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f141,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) | r3_lattices(sK0,X2,k15_lattice3(sK0,X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X3)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f140])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r3_lattices(sK0,X2,k15_lattice3(sK0,X3)) | ~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X3)) )),
% 0.22/0.51    inference(resolution,[],[f138,f125])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_lattices(sK0,X0,k15_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f124,f51])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k15_lattice3(sK0,X1)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f122,f54])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k15_lattice3(sK0,X1)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f115,f79])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))) )),
% 0.22/0.51    inference(resolution,[],[f114,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f110,f51])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f109,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    v10_lattices(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f108,f54])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    ( ! [X0] : (~l3_lattices(sK0) | r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f107,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    v4_lattice3(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f89,f79])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK3(X0,X1,X2)) & r4_lattice3(X0,sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK3(X0,X1,X2)) & r4_lattice3(X0,sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(rectify,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r4_lattice3(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f113,f51])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X2) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f75,f54])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (~l3_lattices(X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X4,X1) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  % (22357)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f43,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(rectify,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f137,f51])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f136,f54])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r3_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 0.22/0.51    inference(resolution,[],[f135,f52])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f134,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f132])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.51    inference(resolution,[],[f81,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.22/0.51  fof(f357,plain,(
% 0.22/0.51    r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f356,f98])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f51])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f96,f54])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(superposition,[],[f79,f95])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ( ! [X0] : (k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f94,f54])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ( ! [X0] : (~l3_lattices(sK0) | k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X0))) )),
% 0.22/0.51    inference(resolution,[],[f70,f51])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).
% 0.22/0.51  fof(f356,plain,(
% 0.22/0.51    ~m1_subset_1(k16_lattice3(sK0,sK2),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.51    inference(resolution,[],[f354,f138])).
% 0.22/0.51  fof(f354,plain,(
% 0.22/0.51    r1_lattices(sK0,k16_lattice3(sK0,sK2),sK1)),
% 0.22/0.51    inference(forward_demodulation,[],[f353,f95])).
% 0.22/0.51  fof(f353,plain,(
% 0.22/0.51    r1_lattices(sK0,k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)),sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f351,f55])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2)),sK1)),
% 0.22/0.51    inference(resolution,[],[f350,f176])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f175,f51])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f174,f52])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f173,f54])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f172,f53])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X4,X0,X1] : (~v4_lattice3(X0) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f90,f79])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f349,f51])).
% 0.22/0.51  fof(f349,plain,(
% 0.22/0.51    r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f348,f54])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f345,f55])).
% 0.22/0.51  fof(f345,plain,(
% 0.22/0.51    r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f344])).
% 0.22/0.51  fof(f344,plain,(
% 0.22/0.51    r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f342,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_lattices(X0,sK5(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f339,f55])).
% 0.22/0.51  fof(f339,plain,(
% 0.22/0.51    r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK1)),
% 0.22/0.51    inference(resolution,[],[f338,f56])).
% 0.22/0.51  fof(f338,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK2) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f318,f322])).
% 0.22/0.51  fof(f322,plain,(
% 0.22/0.51    m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0)) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f321,f55])).
% 0.22/0.51  fof(f321,plain,(
% 0.22/0.51    m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))),
% 0.22/0.51    inference(resolution,[],[f314,f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f103,f51])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f77,f54])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l3_lattices(X0) | r2_hidden(sK5(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r4_lattice3(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    ~r2_hidden(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2)) | m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f313,f51])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f311,f54])).
% 0.22/0.51  fof(f311,plain,(
% 0.22/0.51    m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~r2_hidden(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),a_2_1_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(superposition,[],[f82,f309])).
% 0.22/0.51  fof(f309,plain,(
% 0.22/0.51    sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)) = sK6(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK0,sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f306,f55])).
% 0.22/0.51  fof(f306,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)) = sK6(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK0,sK2)),
% 0.22/0.51    inference(resolution,[],[f297,f155])).
% 0.22/0.51  fof(f297,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r3_lattices(sK0,k16_lattice3(sK0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f296,f98])).
% 0.22/0.51  fof(f296,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,X1),X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f293])).
% 0.22/0.51  fof(f293,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f292,f138])).
% 0.22/0.51  fof(f292,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_lattices(sK0,k16_lattice3(sK0,X1),X0) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f291,f95])).
% 0.22/0.51  fof(f291,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,a_2_1_lattice3(sK0,X1)),X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f288])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,a_2_1_lattice3(sK0,X1)),X0)) )),
% 0.22/0.51    inference(resolution,[],[f287,f176])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f286,f51])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | sK5(sK0,X0,a_2_1_lattice3(sK0,X1)) = sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f106,f54])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ( ! [X4,X5,X3] : (~l3_lattices(X4) | r4_lattice3(sK0,X3,a_2_1_lattice3(X4,X5)) | sK5(sK0,X3,a_2_1_lattice3(X4,X5)) = sK6(sK5(sK0,X3,a_2_1_lattice3(X4,X5)),X4,X5) | ~m1_subset_1(X3,u1_struct_0(sK0)) | v2_struct_0(X4)) )),
% 0.22/0.51    inference(resolution,[],[f104,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sK6(X0,X1,X2) = X0 | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f50])).
% 1.19/0.51  fof(f50,plain,(
% 1.19/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK6(X0,X1,X2),X2) & sK6(X0,X1,X2) = X0 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).
% 1.19/0.51  fof(f49,plain,(
% 1.19/0.51    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK6(X0,X1,X2),X2) & sK6(X0,X1,X2) = X0 & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 1.19/0.51    introduced(choice_axiom,[])).
% 1.19/0.51  fof(f48,plain,(
% 1.19/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.19/0.51    inference(rectify,[],[f47])).
% 1.19/0.51  fof(f47,plain,(
% 1.19/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.19/0.51    inference(nnf_transformation,[],[f28])).
% 1.19/0.51  fof(f28,plain,(
% 1.19/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.19/0.51    inference(flattening,[],[f27])).
% 1.19/0.51  fof(f27,plain,(
% 1.19/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 1.19/0.51    inference(ennf_transformation,[],[f8])).
% 1.19/0.51  fof(f8,axiom,(
% 1.19/0.51    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 1.19/0.51  fof(f82,plain,(
% 1.19/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f50])).
% 1.19/0.51  % (22357)Refutation not found, incomplete strategy% (22357)------------------------------
% 1.19/0.51  % (22357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (22357)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (22357)Memory used [KB]: 10618
% 1.19/0.51  % (22357)Time elapsed: 0.091 s
% 1.19/0.51  % (22357)------------------------------
% 1.19/0.51  % (22357)------------------------------
% 1.19/0.51  fof(f318,plain,(
% 1.19/0.51    ( ! [X0] : (r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0) | ~m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0))) )),
% 1.19/0.51    inference(subsumption_resolution,[],[f317,f51])).
% 1.19/0.51  fof(f317,plain,(
% 1.19/0.51    ( ! [X0] : (r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0) | ~m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.19/0.51    inference(subsumption_resolution,[],[f315,f54])).
% 1.19/0.51  fof(f315,plain,(
% 1.19/0.51    ( ! [X0] : (r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~r2_hidden(X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),X0) | ~m1_subset_1(sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.19/0.51    inference(resolution,[],[f312,f71])).
% 1.19/0.51  fof(f71,plain,(
% 1.19/0.51    ( ! [X4,X2,X0,X1] : (~r3_lattice3(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_lattices(X0,X1,X4) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f41])).
% 1.19/0.51  fof(f41,plain,(
% 1.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 1.19/0.51  fof(f40,plain,(
% 1.19/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.19/0.51    introduced(choice_axiom,[])).
% 1.19/0.51  fof(f39,plain,(
% 1.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.19/0.51    inference(rectify,[],[f38])).
% 1.19/0.51  fof(f38,plain,(
% 1.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.19/0.51    inference(nnf_transformation,[],[f20])).
% 1.19/0.51  fof(f20,plain,(
% 1.19/0.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.19/0.51    inference(flattening,[],[f19])).
% 1.19/0.51  fof(f19,plain,(
% 1.19/0.51    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.19/0.51    inference(ennf_transformation,[],[f3])).
% 1.19/0.51  fof(f3,axiom,(
% 1.19/0.51    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 1.19/0.51  fof(f312,plain,(
% 1.19/0.51    r3_lattice3(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK2) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2))),
% 1.19/0.51    inference(subsumption_resolution,[],[f310,f55])).
% 1.19/0.51  fof(f310,plain,(
% 1.19/0.51    r3_lattice3(sK0,sK5(sK0,sK1,a_2_1_lattice3(sK0,sK2)),sK2) | r4_lattice3(sK0,sK1,a_2_1_lattice3(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.19/0.51    inference(superposition,[],[f165,f309])).
% 1.19/0.51  fof(f165,plain,(
% 1.19/0.51    ( ! [X0,X1] : (r3_lattice3(sK0,sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1) | r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.19/0.51    inference(subsumption_resolution,[],[f164,f51])).
% 1.19/0.51  fof(f164,plain,(
% 1.19/0.51    ( ! [X0,X1] : (r4_lattice3(sK0,X0,a_2_1_lattice3(sK0,X1)) | r3_lattice3(sK0,sK6(sK5(sK0,X0,a_2_1_lattice3(sK0,X1)),sK0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.19/0.51    inference(resolution,[],[f105,f54])).
% 1.19/0.51  fof(f105,plain,(
% 1.19/0.51    ( ! [X2,X0,X1] : (~l3_lattices(X1) | r4_lattice3(sK0,X0,a_2_1_lattice3(X1,X2)) | r3_lattice3(X1,sK6(sK5(sK0,X0,a_2_1_lattice3(X1,X2)),X1,X2),X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(X1)) )),
% 1.19/0.51    inference(resolution,[],[f104,f84])).
% 1.19/0.51  fof(f84,plain,(
% 1.19/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | r3_lattice3(X1,sK6(X0,X1,X2),X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.19/0.51    inference(cnf_transformation,[],[f50])).
% 1.19/0.51  % SZS output end Proof for theBenchmark
% 1.19/0.51  % (22378)------------------------------
% 1.19/0.51  % (22378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (22378)Termination reason: Refutation
% 1.19/0.51  
% 1.19/0.51  % (22378)Memory used [KB]: 6396
% 1.19/0.51  % (22378)Time elapsed: 0.093 s
% 1.19/0.51  % (22378)------------------------------
% 1.19/0.51  % (22378)------------------------------
% 1.19/0.51  % (22358)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.51  % (22356)Success in time 0.149 s
%------------------------------------------------------------------------------
