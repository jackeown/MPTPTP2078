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
% DateTime   : Thu Dec  3 13:15:46 EST 2020

% Result     : Theorem 4.57s
% Output     : Refutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :  195 (9618 expanded)
%              Number of leaves         :   20 (3620 expanded)
%              Depth                    :   30
%              Number of atoms          : 1121 (89545 expanded)
%              Number of equality atoms :   91 (1305 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9936,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9935,f6876])).

fof(f6876,plain,(
    r2_hidden(sK3(sK8(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) ),
    inference(subsumption_resolution,[],[f6848,f5689])).

fof(f5689,plain,(
    r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1) ),
    inference(subsumption_resolution,[],[f5688,f70])).

fof(f70,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
    & ! [X3] :
        ( ( r2_hidden(sK3(X3),sK2)
          & r3_lattices(sK0,X3,sK3(X3))
          & m1_subset_1(sK3(X3),u1_struct_0(sK0)) )
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
            & ! [X3] :
                ( ? [X4] :
                    ( r2_hidden(X4,X2)
                    & r3_lattices(X0,X3,X4)
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ~ r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(sK0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2,X1] :
        ( ~ r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2))
        & ! [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(sK0,X3,X4)
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )
   => ( ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))
      & ! [X3] :
          ( ? [X4] :
              ( r2_hidden(X4,sK2)
              & r3_lattices(sK0,X3,X4)
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          | ~ r2_hidden(X3,sK1)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X3] :
      ( ? [X4] :
          ( r2_hidden(X4,sK2)
          & r3_lattices(sK0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(sK0)) )
     => ( r2_hidden(sK3(X3),sK2)
        & r3_lattices(sK0,X3,sK3(X3))
        & m1_subset_1(sK3(X3),u1_struct_0(sK0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( r2_hidden(X4,X2)
                            & r3_lattices(X0,X3,X4) ) )
                    & r2_hidden(X3,X1) ) )
           => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

fof(f5688,plain,
    ( r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f5687,f73])).

fof(f73,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f5687,plain,
    ( r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f5679,f4856])).

fof(f4856,plain,(
    ! [X9] : m1_subset_1(k15_lattice3(sK0,X9),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f349,f4839])).

fof(f4839,plain,(
    ! [X1] : k15_lattice3(sK0,X1) = sK7(sK0,X1) ),
    inference(subsumption_resolution,[],[f4838,f740])).

fof(f740,plain,(
    ! [X6] :
      ( m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0))
      | k15_lattice3(sK0,X6) = sK7(sK0,X6) ) ),
    inference(subsumption_resolution,[],[f739,f70])).

fof(f739,plain,(
    ! [X6] :
      ( k15_lattice3(sK0,X6) = sK7(sK0,X6)
      | m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f738,f71])).

fof(f71,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f738,plain,(
    ! [X6] :
      ( k15_lattice3(sK0,X6) = sK7(sK0,X6)
      | m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f737,f72])).

fof(f72,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f737,plain,(
    ! [X6] :
      ( k15_lattice3(sK0,X6) = sK7(sK0,X6)
      | m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f736,f73])).

fof(f736,plain,(
    ! [X6] :
      ( k15_lattice3(sK0,X6) = sK7(sK0,X6)
      | m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f709,f349])).

fof(f709,plain,(
    ! [X6] :
      ( k15_lattice3(sK0,X6) = sK7(sK0,X6)
      | m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0))
      | ~ m1_subset_1(sK7(sK0,X6),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f351,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
                & r4_lattice3(X0,sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
        & r4_lattice3(X0,sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f351,plain,(
    ! [X10] : r4_lattice3(sK0,sK7(sK0,X10),X10) ),
    inference(subsumption_resolution,[],[f350,f70])).

fof(f350,plain,(
    ! [X10] :
      ( r4_lattice3(sK0,sK7(sK0,X10),X10)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f295,f72])).

fof(f295,plain,(
    ! [X10] :
      ( r4_lattice3(sK0,sK7(sK0,X10),X10)
      | ~ v4_lattice3(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f95])).

fof(f95,plain,(
    ! [X4,X0] :
      ( r4_lattice3(X0,sK7(X0,X4),X4)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ! [X2] :
              ( ( ~ r1_lattices(X0,X2,sK6(X0,X2))
                & r4_lattice3(X0,sK6(X0,X2),sK5(X0))
                & m1_subset_1(sK6(X0,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,sK5(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X6] :
                  ( r1_lattices(X0,sK7(X0,X4),X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,sK7(X0,X4),X4)
              & m1_subset_1(sK7(X0,X4),u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X2,X3)
              & r4_lattice3(X0,X3,sK5(X0))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r4_lattice3(X0,X2,sK5(X0))
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,sK5(X0))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK6(X0,X2))
        & r4_lattice3(X0,sK6(X0,X2),sK5(X0))
        & m1_subset_1(sK6(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_lattices(X0,X5,X6)
              | ~ r4_lattice3(X0,X6,X4)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r4_lattice3(X0,X5,X4)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_lattices(X0,sK7(X0,X4),X6)
            | ~ r4_lattice3(X0,X6,X4)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r4_lattice3(X0,sK7(X0,X4),X4)
        & m1_subset_1(sK7(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X4] :
            ? [X5] :
              ( ! [X6] :
                  ( r1_lattices(X0,X5,X6)
                  | ~ r4_lattice3(X0,X6,X4)
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              & r4_lattice3(X0,X5,X4)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ? [X1] :
            ! [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
        & ( ! [X1] :
            ? [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v4_lattice3(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f4838,plain,(
    ! [X1] :
      ( k15_lattice3(sK0,X1) = sK7(sK0,X1)
      | ~ m1_subset_1(sK4(sK0,X1,sK7(sK0,X1)),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f4834,f735])).

fof(f735,plain,(
    ! [X5] :
      ( r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5)
      | k15_lattice3(sK0,X5) = sK7(sK0,X5) ) ),
    inference(subsumption_resolution,[],[f734,f70])).

fof(f734,plain,(
    ! [X5] :
      ( k15_lattice3(sK0,X5) = sK7(sK0,X5)
      | r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f733,f71])).

fof(f733,plain,(
    ! [X5] :
      ( k15_lattice3(sK0,X5) = sK7(sK0,X5)
      | r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f732,f72])).

fof(f732,plain,(
    ! [X5] :
      ( k15_lattice3(sK0,X5) = sK7(sK0,X5)
      | r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f731,f73])).

fof(f731,plain,(
    ! [X5] :
      ( k15_lattice3(sK0,X5) = sK7(sK0,X5)
      | r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f708,f349])).

fof(f708,plain,(
    ! [X5] :
      ( k15_lattice3(sK0,X5) = sK7(sK0,X5)
      | r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5)
      | ~ m1_subset_1(sK7(sK0,X5),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f351,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | r4_lattice3(X0,sK4(X0,X1,X2),X1)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | r4_lattice3(X0,sK4(X0,X1,X2),X1)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4834,plain,(
    ! [X1] :
      ( k15_lattice3(sK0,X1) = sK7(sK0,X1)
      | ~ r4_lattice3(sK0,sK4(sK0,X1,sK7(sK0,X1)),X1)
      | ~ m1_subset_1(sK4(sK0,X1,sK7(sK0,X1)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f730,f353])).

fof(f353,plain,(
    ! [X12,X11] :
      ( r1_lattices(sK0,sK7(sK0,X11),X12)
      | ~ r4_lattice3(sK0,X12,X11)
      | ~ m1_subset_1(X12,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f352,f70])).

fof(f352,plain,(
    ! [X12,X11] :
      ( r1_lattices(sK0,sK7(sK0,X11),X12)
      | ~ r4_lattice3(sK0,X12,X11)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f296,f72])).

fof(f296,plain,(
    ! [X12,X11] :
      ( r1_lattices(sK0,sK7(sK0,X11),X12)
      | ~ r4_lattice3(sK0,X12,X11)
      | ~ m1_subset_1(X12,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f96])).

fof(f96,plain,(
    ! [X6,X4,X0] :
      ( r1_lattices(X0,sK7(X0,X4),X6)
      | ~ r4_lattice3(X0,X6,X4)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f730,plain,(
    ! [X4] :
      ( ~ r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4)))
      | k15_lattice3(sK0,X4) = sK7(sK0,X4) ) ),
    inference(subsumption_resolution,[],[f729,f70])).

fof(f729,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = sK7(sK0,X4)
      | ~ r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f728,f71])).

fof(f728,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = sK7(sK0,X4)
      | ~ r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4)))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f727,f72])).

fof(f727,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = sK7(sK0,X4)
      | ~ r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4)))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f726,f73])).

fof(f726,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = sK7(sK0,X4)
      | ~ r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4)))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f707,f349])).

fof(f707,plain,(
    ! [X4] :
      ( k15_lattice3(sK0,X4) = sK7(sK0,X4)
      | ~ r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4)))
      | ~ m1_subset_1(sK7(sK0,X4),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f351,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X1) = X2
      | ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f349,plain,(
    ! [X9] : m1_subset_1(sK7(sK0,X9),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f348,f70])).

fof(f348,plain,(
    ! [X9] :
      ( m1_subset_1(sK7(sK0,X9),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f294,f72])).

fof(f294,plain,(
    ! [X9] :
      ( m1_subset_1(sK7(sK0,X9),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f94])).

fof(f94,plain,(
    ! [X4,X0] :
      ( m1_subset_1(sK7(X0,X4),u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f5679,plain,
    ( r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f5645,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK8(X0,X1,X2),X1)
                  & r2_hidden(sK8(X0,X1,X2),X2)
                  & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK8(X0,X1,X2),X1)
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f5645,plain,(
    ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1) ),
    inference(resolution,[],[f4907,f1874])).

fof(f1874,plain,(
    ~ r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1)) ),
    inference(resolution,[],[f1580,f77])).

fof(f77,plain,(
    ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f1580,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f1563,f854])).

fof(f854,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f853,f70])).

fof(f853,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f852,f71])).

fof(f852,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f851,f72])).

fof(f851,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f850,f73])).

fof(f850,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f847])).

fof(f847,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK0,X1)) ) ),
    inference(superposition,[],[f106,f365])).

fof(f365,plain,(
    ! [X31,X32] :
      ( sK9(X31,sK0,X32) = X31
      | ~ r2_hidden(X31,a_2_2_lattice3(sK0,X32)) ) ),
    inference(subsumption_resolution,[],[f364,f70])).

fof(f364,plain,(
    ! [X31,X32] :
      ( sK9(X31,sK0,X32) = X31
      | ~ r2_hidden(X31,a_2_2_lattice3(sK0,X32))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f363,f71])).

fof(f363,plain,(
    ! [X31,X32] :
      ( sK9(X31,sK0,X32) = X31
      | ~ r2_hidden(X31,a_2_2_lattice3(sK0,X32))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f307,f72])).

fof(f307,plain,(
    ! [X31,X32] :
      ( sK9(X31,sK0,X32) = X31
      | ~ r2_hidden(X31,a_2_2_lattice3(sK0,X32))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( sK9(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK9(X0,X1,X2),X2)
            & sK9(X0,X1,X2) = X0
            & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK9(X0,X1,X2),X2)
        & sK9(X0,X1,X2) = X0
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1563,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,k15_lattice3(sK0,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f347,f329])).

fof(f329,plain,(
    ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) ),
    inference(subsumption_resolution,[],[f328,f70])).

fof(f328,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f327,f71])).

fof(f327,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f287,f72])).

fof(f287,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(f347,plain,(
    ! [X8,X7] :
      ( r3_lattices(sK0,k16_lattice3(sK0,X7),X8)
      | ~ r2_hidden(X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f346,f70])).

fof(f346,plain,(
    ! [X8,X7] :
      ( r3_lattices(sK0,k16_lattice3(sK0,X7),X8)
      | ~ r2_hidden(X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f345,f71])).

fof(f345,plain,(
    ! [X8,X7] :
      ( r3_lattices(sK0,k16_lattice3(sK0,X7),X8)
      | ~ r2_hidden(X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f293,f72])).

fof(f293,plain,(
    ! [X8,X7] :
      ( r3_lattices(sK0,k16_lattice3(sK0,X7),X8)
      | ~ r2_hidden(X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(f4907,plain,(
    ! [X33,X32] :
      ( r2_hidden(k15_lattice3(sK0,X32),a_2_2_lattice3(sK0,X33))
      | ~ r4_lattice3(sK0,k15_lattice3(sK0,X32),X33) ) ),
    inference(forward_demodulation,[],[f4873,f4839])).

fof(f4873,plain,(
    ! [X33,X32] :
      ( r2_hidden(k15_lattice3(sK0,X32),a_2_2_lattice3(sK0,X33))
      | ~ r4_lattice3(sK0,sK7(sK0,X32),X33) ) ),
    inference(backward_demodulation,[],[f679,f4839])).

fof(f679,plain,(
    ! [X33,X32] :
      ( r2_hidden(sK7(sK0,X32),a_2_2_lattice3(sK0,X33))
      | ~ r4_lattice3(sK0,sK7(sK0,X32),X33) ) ),
    inference(subsumption_resolution,[],[f678,f70])).

fof(f678,plain,(
    ! [X33,X32] :
      ( r2_hidden(sK7(sK0,X32),a_2_2_lattice3(sK0,X33))
      | ~ r4_lattice3(sK0,sK7(sK0,X32),X33)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f677,f71])).

fof(f677,plain,(
    ! [X33,X32] :
      ( r2_hidden(sK7(sK0,X32),a_2_2_lattice3(sK0,X33))
      | ~ r4_lattice3(sK0,sK7(sK0,X32),X33)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f676,f72])).

fof(f676,plain,(
    ! [X33,X32] :
      ( r2_hidden(sK7(sK0,X32),a_2_2_lattice3(sK0,X33))
      | ~ r4_lattice3(sK0,sK7(sK0,X32),X33)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f620,f73])).

fof(f620,plain,(
    ! [X33,X32] :
      ( r2_hidden(sK7(sK0,X32),a_2_2_lattice3(sK0,X33))
      | ~ r4_lattice3(sK0,sK7(sK0,X32),X33)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f349,f118])).

fof(f118,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f6848,plain,
    ( ~ r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | r2_hidden(sK3(sK8(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) ),
    inference(resolution,[],[f5686,f76])).

fof(f76,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(sK3(X3),sK2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5686,plain,(
    m1_subset_1(sK8(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f5685,f70])).

fof(f5685,plain,
    ( m1_subset_1(sK8(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f5684,f73])).

fof(f5684,plain,
    ( m1_subset_1(sK8(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f5678,f4856])).

fof(f5678,plain,
    ( m1_subset_1(sK8(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f5645,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f9935,plain,(
    ~ r2_hidden(sK3(sK8(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) ),
    inference(subsumption_resolution,[],[f9934,f5689])).

fof(f9934,plain,
    ( ~ r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ r2_hidden(sK3(sK8(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) ),
    inference(subsumption_resolution,[],[f9928,f5686])).

fof(f9928,plain,
    ( ~ m1_subset_1(sK8(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1)
    | ~ r2_hidden(sK3(sK8(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) ),
    inference(resolution,[],[f9327,f579])).

fof(f579,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(sK3(X0),X1) ) ),
    inference(subsumption_resolution,[],[f578,f74])).

fof(f74,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(X3),u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f578,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ r2_hidden(sK3(X0),X1)
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f577,f70])).

fof(f577,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ r2_hidden(sK3(X0),X1)
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f576,f71])).

fof(f576,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ r2_hidden(sK3(X0),X1)
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f575,f72])).

fof(f575,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ r2_hidden(sK3(X0),X1)
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f574,f73])).

fof(f574,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ r2_hidden(sK3(X0),X1)
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f571])).

fof(f571,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ r2_hidden(sK3(X0),X1)
      | ~ m1_subset_1(sK3(X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f75,f119])).

fof(f119,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X3,a_2_5_lattice3(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r3_lattices(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r3_lattices(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK11(X0,X1,X2),X2)
            & r3_lattices(X1,sK10(X0,X1,X2),sK11(X0,X1,X2))
            & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))
            & sK10(X0,X1,X2) = X0
            & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f66,f68,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r3_lattices(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r3_lattices(X1,sK10(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK10(X0,X1,X2) = X0
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,sK10(X0,X1,X2),X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK11(X0,X1,X2),X2)
        & r3_lattices(X1,sK10(X0,X1,X2),sK11(X0,X1,X2))
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r3_lattices(X1,X5,X6)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X1,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

fof(f75,plain,(
    ! [X3] :
      ( r3_lattices(sK0,X3,sK3(X3))
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9327,plain,(
    ~ r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f5692,f5320])).

fof(f5320,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f5319,f870])).

fof(f870,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f869,f70])).

fof(f869,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f868,f71])).

fof(f868,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f867,f72])).

fof(f867,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f866,f73])).

fof(f866,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f863])).

fof(f863,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1)) ) ),
    inference(superposition,[],[f110,f374])).

fof(f374,plain,(
    ! [X37,X38] :
      ( sK10(X37,sK0,X38) = X37
      | ~ r2_hidden(X37,a_2_5_lattice3(sK0,X38)) ) ),
    inference(subsumption_resolution,[],[f373,f70])).

fof(f373,plain,(
    ! [X37,X38] :
      ( sK10(X37,sK0,X38) = X37
      | ~ r2_hidden(X37,a_2_5_lattice3(sK0,X38))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f372,f71])).

fof(f372,plain,(
    ! [X37,X38] :
      ( sK10(X37,sK0,X38) = X37
      | ~ r2_hidden(X37,a_2_5_lattice3(sK0,X38))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f310,f72])).

fof(f310,plain,(
    ! [X37,X38] :
      ( sK10(X37,sK0,X38) = X37
      | ~ r2_hidden(X37,a_2_5_lattice3(sK0,X38))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( sK10(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f5319,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f5303,f4856])).

fof(f5303,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_5_lattice3(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
      | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f5059,f354])).

fof(f354,plain,(
    ! [X17,X18,X16] :
      ( ~ r4_lattice3(sK0,X17,X18)
      | ~ r2_hidden(X16,X18)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | r1_lattices(sK0,X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f300,f70])).

fof(f300,plain,(
    ! [X17,X18,X16] :
      ( r1_lattices(sK0,X16,X17)
      | ~ r2_hidden(X16,X18)
      | ~ m1_subset_1(X16,u1_struct_0(sK0))
      | ~ r4_lattice3(sK0,X17,X18)
      | ~ m1_subset_1(X17,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X4,X1)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f5059,plain,(
    ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0)) ),
    inference(superposition,[],[f4857,f332])).

fof(f332,plain,(
    ! [X1] : k15_lattice3(sK0,X1) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X1)) ),
    inference(subsumption_resolution,[],[f331,f70])).

fof(f331,plain,(
    ! [X1] :
      ( k15_lattice3(sK0,X1) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f330,f71])).

fof(f330,plain,(
    ! [X1] :
      ( k15_lattice3(sK0,X1) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f288,f72])).

fof(f288,plain,(
    ! [X1] :
      ( k15_lattice3(sK0,X1) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X1))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f73,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

fof(f4857,plain,(
    ! [X10] : r4_lattice3(sK0,k15_lattice3(sK0,X10),X10) ),
    inference(backward_demodulation,[],[f351,f4839])).

fof(f5692,plain,(
    ~ r1_lattices(sK0,sK8(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f5691,f70])).

fof(f5691,plain,
    ( ~ r1_lattices(sK0,sK8(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f5690,f73])).

fof(f5690,plain,
    ( ~ r1_lattices(sK0,sK8(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f5680,f4856])).

fof(f5680,plain,
    ( ~ r1_lattices(sK0,sK8(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f5645,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | ~ r1_lattices(X0,sK8(X0,X1,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (12060)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.48  % (12082)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (12073)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (12065)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (12069)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (12061)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (12071)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (12064)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (12063)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (12076)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (12079)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (12083)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (12072)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (12078)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (12058)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (12068)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (12066)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (12085)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (12077)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (12072)Refutation not found, incomplete strategy% (12072)------------------------------
% 0.20/0.51  % (12072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12067)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (12058)Refutation not found, incomplete strategy% (12058)------------------------------
% 0.20/0.52  % (12058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12058)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12058)Memory used [KB]: 10618
% 0.20/0.52  % (12058)Time elapsed: 0.114 s
% 0.20/0.52  % (12058)------------------------------
% 0.20/0.52  % (12058)------------------------------
% 0.20/0.52  % (12075)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (12070)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (12072)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12072)Memory used [KB]: 6140
% 0.20/0.52  % (12072)Time elapsed: 0.118 s
% 0.20/0.52  % (12072)------------------------------
% 0.20/0.52  % (12072)------------------------------
% 0.20/0.52  % (12084)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (12074)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (12081)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (12070)Refutation not found, incomplete strategy% (12070)------------------------------
% 0.20/0.53  % (12070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12062)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  % (12070)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (12070)Memory used [KB]: 10618
% 0.20/0.53  % (12070)Time elapsed: 0.124 s
% 0.20/0.53  % (12070)------------------------------
% 0.20/0.53  % (12070)------------------------------
% 2.04/0.62  % (12068)Refutation not found, incomplete strategy% (12068)------------------------------
% 2.04/0.62  % (12068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.62  % (12068)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.62  
% 2.04/0.62  % (12068)Memory used [KB]: 6140
% 2.04/0.62  % (12068)Time elapsed: 0.210 s
% 2.04/0.62  % (12068)------------------------------
% 2.04/0.62  % (12068)------------------------------
% 4.17/0.89  % (12073)Time limit reached!
% 4.17/0.89  % (12073)------------------------------
% 4.17/0.89  % (12073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.89  % (12073)Termination reason: Time limit
% 4.17/0.89  % (12073)Termination phase: Saturation
% 4.17/0.89  
% 4.17/0.89  % (12073)Memory used [KB]: 7547
% 4.17/0.89  % (12073)Time elapsed: 0.506 s
% 4.17/0.89  % (12073)------------------------------
% 4.17/0.89  % (12073)------------------------------
% 4.57/0.96  % (12077)Refutation found. Thanks to Tanya!
% 4.57/0.96  % SZS status Theorem for theBenchmark
% 4.57/0.96  % SZS output start Proof for theBenchmark
% 4.57/0.96  fof(f9936,plain,(
% 4.57/0.96    $false),
% 4.57/0.96    inference(subsumption_resolution,[],[f9935,f6876])).
% 4.57/0.96  fof(f6876,plain,(
% 4.57/0.96    r2_hidden(sK3(sK8(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)),
% 4.57/0.96    inference(subsumption_resolution,[],[f6848,f5689])).
% 4.57/0.96  fof(f5689,plain,(
% 4.57/0.96    r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1)),
% 4.57/0.96    inference(subsumption_resolution,[],[f5688,f70])).
% 4.57/0.96  fof(f70,plain,(
% 4.57/0.96    ~v2_struct_0(sK0)),
% 4.57/0.96    inference(cnf_transformation,[],[f44])).
% 4.57/0.96  fof(f44,plain,(
% 4.57/0.96    (~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) & ! [X3] : ((r2_hidden(sK3(X3),sK2) & r3_lattices(sK0,X3,sK3(X3)) & m1_subset_1(sK3(X3),u1_struct_0(sK0))) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 4.57/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f43,f42,f41])).
% 4.57/0.96  fof(f41,plain,(
% 4.57/0.96    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : (~r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(sK0)))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f42,plain,(
% 4.57/0.96    ? [X2,X1] : (~r3_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(sK0)))) => (~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) & ! [X3] : (? [X4] : (r2_hidden(X4,sK2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f43,plain,(
% 4.57/0.96    ! [X3] : (? [X4] : (r2_hidden(X4,sK2) & r3_lattices(sK0,X3,X4) & m1_subset_1(X4,u1_struct_0(sK0))) => (r2_hidden(sK3(X3),sK2) & r3_lattices(sK0,X3,sK3(X3)) & m1_subset_1(sK3(X3),u1_struct_0(sK0))))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f18,plain,(
% 4.57/0.96    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 4.57/0.96    inference(flattening,[],[f17])).
% 4.57/0.96  fof(f17,plain,(
% 4.57/0.96    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : ((? [X4] : ((r2_hidden(X4,X2) & r3_lattices(X0,X3,X4)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f13])).
% 4.57/0.96  fof(f13,negated_conjecture,(
% 4.57/0.96    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 4.57/0.96    inference(negated_conjecture,[],[f12])).
% 4.57/0.96  fof(f12,conjecture,(
% 4.57/0.96    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 4.57/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).
% 4.57/0.96  fof(f5688,plain,(
% 4.57/0.96    r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | v2_struct_0(sK0)),
% 4.57/0.96    inference(subsumption_resolution,[],[f5687,f73])).
% 4.57/0.96  fof(f73,plain,(
% 4.57/0.96    l3_lattices(sK0)),
% 4.57/0.96    inference(cnf_transformation,[],[f44])).
% 4.57/0.96  fof(f5687,plain,(
% 4.57/0.96    r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 4.57/0.96    inference(subsumption_resolution,[],[f5679,f4856])).
% 4.57/0.96  fof(f4856,plain,(
% 4.57/0.96    ( ! [X9] : (m1_subset_1(k15_lattice3(sK0,X9),u1_struct_0(sK0))) )),
% 4.57/0.96    inference(backward_demodulation,[],[f349,f4839])).
% 4.57/0.96  fof(f4839,plain,(
% 4.57/0.96    ( ! [X1] : (k15_lattice3(sK0,X1) = sK7(sK0,X1)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f4838,f740])).
% 4.57/0.96  fof(f740,plain,(
% 4.57/0.96    ( ! [X6] : (m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0)) | k15_lattice3(sK0,X6) = sK7(sK0,X6)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f739,f70])).
% 4.57/0.96  fof(f739,plain,(
% 4.57/0.96    ( ! [X6] : (k15_lattice3(sK0,X6) = sK7(sK0,X6) | m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f738,f71])).
% 4.57/0.96  fof(f71,plain,(
% 4.57/0.96    v10_lattices(sK0)),
% 4.57/0.96    inference(cnf_transformation,[],[f44])).
% 4.57/0.96  fof(f738,plain,(
% 4.57/0.96    ( ! [X6] : (k15_lattice3(sK0,X6) = sK7(sK0,X6) | m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f737,f72])).
% 4.57/0.96  fof(f72,plain,(
% 4.57/0.96    v4_lattice3(sK0)),
% 4.57/0.96    inference(cnf_transformation,[],[f44])).
% 4.57/0.96  fof(f737,plain,(
% 4.57/0.96    ( ! [X6] : (k15_lattice3(sK0,X6) = sK7(sK0,X6) | m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f736,f73])).
% 4.57/0.96  fof(f736,plain,(
% 4.57/0.96    ( ! [X6] : (k15_lattice3(sK0,X6) = sK7(sK0,X6) | m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f709,f349])).
% 4.57/0.96  fof(f709,plain,(
% 4.57/0.96    ( ! [X6] : (k15_lattice3(sK0,X6) = sK7(sK0,X6) | m1_subset_1(sK4(sK0,X6,sK7(sK0,X6)),u1_struct_0(sK0)) | ~m1_subset_1(sK7(sK0,X6),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f351,f122])).
% 4.57/0.96  fof(f122,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(duplicate_literal_removal,[],[f91])).
% 4.57/0.96  fof(f91,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f49])).
% 4.57/0.96  fof(f49,plain,(
% 4.57/0.96    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).
% 4.57/0.96  fof(f48,plain,(
% 4.57/0.96    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f47,plain,(
% 4.57/0.96    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(rectify,[],[f46])).
% 4.57/0.96  fof(f46,plain,(
% 4.57/0.96    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(flattening,[],[f45])).
% 4.57/0.96  fof(f45,plain,(
% 4.57/0.96    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(nnf_transformation,[],[f30])).
% 4.57/0.96  fof(f30,plain,(
% 4.57/0.96    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(flattening,[],[f29])).
% 4.57/0.96  fof(f29,plain,(
% 4.57/0.96    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f5])).
% 4.57/0.96  fof(f5,axiom,(
% 4.57/0.96    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 4.57/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 4.57/0.96  fof(f351,plain,(
% 4.57/0.96    ( ! [X10] : (r4_lattice3(sK0,sK7(sK0,X10),X10)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f350,f70])).
% 4.57/0.96  fof(f350,plain,(
% 4.57/0.96    ( ! [X10] : (r4_lattice3(sK0,sK7(sK0,X10),X10) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f295,f72])).
% 4.57/0.96  fof(f295,plain,(
% 4.57/0.96    ( ! [X10] : (r4_lattice3(sK0,sK7(sK0,X10),X10) | ~v4_lattice3(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f73,f95])).
% 4.57/0.96  fof(f95,plain,(
% 4.57/0.96    ( ! [X4,X0] : (r4_lattice3(X0,sK7(X0,X4),X4) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f55])).
% 4.57/0.96  fof(f55,plain,(
% 4.57/0.96    ! [X0] : (((v4_lattice3(X0) | ! [X2] : ((~r1_lattices(X0,X2,sK6(X0,X2)) & r4_lattice3(X0,sK6(X0,X2),sK5(X0)) & m1_subset_1(sK6(X0,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK5(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X6] : (r1_lattices(X0,sK7(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK7(X0,X4),X4) & m1_subset_1(sK7(X0,X4),u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f51,f54,f53,f52])).
% 4.57/0.96  fof(f52,plain,(
% 4.57/0.96    ! [X0] : (? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) => ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,sK5(X0)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,sK5(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f53,plain,(
% 4.57/0.96    ! [X2,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,sK5(X0)) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK6(X0,X2)) & r4_lattice3(X0,sK6(X0,X2),sK5(X0)) & m1_subset_1(sK6(X0,X2),u1_struct_0(X0))))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f54,plain,(
% 4.57/0.96    ! [X4,X0] : (? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r1_lattices(X0,sK7(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,sK7(X0,X4),X4) & m1_subset_1(sK7(X0,X4),u1_struct_0(X0))))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f51,plain,(
% 4.57/0.96    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : ? [X5] : (! [X6] : (r1_lattices(X0,X5,X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0))) & r4_lattice3(X0,X5,X4) & m1_subset_1(X5,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(rectify,[],[f50])).
% 4.57/0.96  fof(f50,plain,(
% 4.57/0.96    ! [X0] : (((v4_lattice3(X0) | ? [X1] : ! [X2] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~v4_lattice3(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(nnf_transformation,[],[f32])).
% 4.57/0.96  fof(f32,plain,(
% 4.57/0.96    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(flattening,[],[f31])).
% 4.57/0.96  fof(f31,plain,(
% 4.57/0.96    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f4])).
% 4.57/0.96  fof(f4,axiom,(
% 4.57/0.96    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 4.57/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattice3)).
% 4.57/0.96  fof(f4838,plain,(
% 4.57/0.96    ( ! [X1] : (k15_lattice3(sK0,X1) = sK7(sK0,X1) | ~m1_subset_1(sK4(sK0,X1,sK7(sK0,X1)),u1_struct_0(sK0))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f4834,f735])).
% 4.57/0.96  fof(f735,plain,(
% 4.57/0.96    ( ! [X5] : (r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5) | k15_lattice3(sK0,X5) = sK7(sK0,X5)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f734,f70])).
% 4.57/0.96  fof(f734,plain,(
% 4.57/0.96    ( ! [X5] : (k15_lattice3(sK0,X5) = sK7(sK0,X5) | r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f733,f71])).
% 4.57/0.96  fof(f733,plain,(
% 4.57/0.96    ( ! [X5] : (k15_lattice3(sK0,X5) = sK7(sK0,X5) | r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f732,f72])).
% 4.57/0.96  fof(f732,plain,(
% 4.57/0.96    ( ! [X5] : (k15_lattice3(sK0,X5) = sK7(sK0,X5) | r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f731,f73])).
% 4.57/0.96  fof(f731,plain,(
% 4.57/0.96    ( ! [X5] : (k15_lattice3(sK0,X5) = sK7(sK0,X5) | r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f708,f349])).
% 4.57/0.96  fof(f708,plain,(
% 4.57/0.96    ( ! [X5] : (k15_lattice3(sK0,X5) = sK7(sK0,X5) | r4_lattice3(sK0,sK4(sK0,X5,sK7(sK0,X5)),X5) | ~m1_subset_1(sK7(sK0,X5),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f351,f121])).
% 4.57/0.96  fof(f121,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK4(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(duplicate_literal_removal,[],[f92])).
% 4.57/0.96  fof(f92,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | r4_lattice3(X0,sK4(X0,X1,X2),X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f49])).
% 4.57/0.96  fof(f4834,plain,(
% 4.57/0.96    ( ! [X1] : (k15_lattice3(sK0,X1) = sK7(sK0,X1) | ~r4_lattice3(sK0,sK4(sK0,X1,sK7(sK0,X1)),X1) | ~m1_subset_1(sK4(sK0,X1,sK7(sK0,X1)),u1_struct_0(sK0))) )),
% 4.57/0.96    inference(resolution,[],[f730,f353])).
% 4.57/0.96  fof(f353,plain,(
% 4.57/0.96    ( ! [X12,X11] : (r1_lattices(sK0,sK7(sK0,X11),X12) | ~r4_lattice3(sK0,X12,X11) | ~m1_subset_1(X12,u1_struct_0(sK0))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f352,f70])).
% 4.57/0.96  fof(f352,plain,(
% 4.57/0.96    ( ! [X12,X11] : (r1_lattices(sK0,sK7(sK0,X11),X12) | ~r4_lattice3(sK0,X12,X11) | ~m1_subset_1(X12,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f296,f72])).
% 4.57/0.96  fof(f296,plain,(
% 4.57/0.96    ( ! [X12,X11] : (r1_lattices(sK0,sK7(sK0,X11),X12) | ~r4_lattice3(sK0,X12,X11) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~v4_lattice3(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f73,f96])).
% 4.57/0.96  fof(f96,plain,(
% 4.57/0.96    ( ! [X6,X4,X0] : (r1_lattices(X0,sK7(X0,X4),X6) | ~r4_lattice3(X0,X6,X4) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f55])).
% 4.57/0.96  fof(f730,plain,(
% 4.57/0.96    ( ! [X4] : (~r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4))) | k15_lattice3(sK0,X4) = sK7(sK0,X4)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f729,f70])).
% 4.57/0.96  fof(f729,plain,(
% 4.57/0.96    ( ! [X4] : (k15_lattice3(sK0,X4) = sK7(sK0,X4) | ~r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4))) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f728,f71])).
% 4.57/0.96  fof(f728,plain,(
% 4.57/0.96    ( ! [X4] : (k15_lattice3(sK0,X4) = sK7(sK0,X4) | ~r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4))) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f727,f72])).
% 4.57/0.96  fof(f727,plain,(
% 4.57/0.96    ( ! [X4] : (k15_lattice3(sK0,X4) = sK7(sK0,X4) | ~r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f726,f73])).
% 4.57/0.96  fof(f726,plain,(
% 4.57/0.96    ( ! [X4] : (k15_lattice3(sK0,X4) = sK7(sK0,X4) | ~r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f707,f349])).
% 4.57/0.96  fof(f707,plain,(
% 4.57/0.96    ( ! [X4] : (k15_lattice3(sK0,X4) = sK7(sK0,X4) | ~r1_lattices(sK0,sK7(sK0,X4),sK4(sK0,X4,sK7(sK0,X4))) | ~m1_subset_1(sK7(sK0,X4),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f351,f120])).
% 4.57/0.96  fof(f120,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK4(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(duplicate_literal_removal,[],[f93])).
% 4.57/0.96  fof(f93,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (k15_lattice3(X0,X1) = X2 | ~r1_lattices(X0,X2,sK4(X0,X1,X2)) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f49])).
% 4.57/0.96  fof(f349,plain,(
% 4.57/0.96    ( ! [X9] : (m1_subset_1(sK7(sK0,X9),u1_struct_0(sK0))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f348,f70])).
% 4.57/0.96  fof(f348,plain,(
% 4.57/0.96    ( ! [X9] : (m1_subset_1(sK7(sK0,X9),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f294,f72])).
% 4.57/0.96  fof(f294,plain,(
% 4.57/0.96    ( ! [X9] : (m1_subset_1(sK7(sK0,X9),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f73,f94])).
% 4.57/0.96  fof(f94,plain,(
% 4.57/0.96    ( ! [X4,X0] : (m1_subset_1(sK7(X0,X4),u1_struct_0(X0)) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f55])).
% 4.57/0.96  fof(f5679,plain,(
% 4.57/0.96    r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 4.57/0.96    inference(resolution,[],[f5645,f102])).
% 4.57/0.96  fof(f102,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | r2_hidden(sK8(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f59])).
% 4.57/0.96  fof(f59,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f57,f58])).
% 4.57/0.96  fof(f58,plain,(
% 4.57/0.96    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK8(X0,X1,X2),X1) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f57,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(rectify,[],[f56])).
% 4.57/0.96  fof(f56,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(nnf_transformation,[],[f34])).
% 4.57/0.96  fof(f34,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(flattening,[],[f33])).
% 4.57/0.96  fof(f33,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f3])).
% 4.57/0.96  fof(f3,axiom,(
% 4.57/0.96    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 4.57/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 4.57/0.96  fof(f5645,plain,(
% 4.57/0.96    ~r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)),
% 4.57/0.96    inference(resolution,[],[f4907,f1874])).
% 4.57/0.96  fof(f1874,plain,(
% 4.57/0.96    ~r2_hidden(k15_lattice3(sK0,sK2),a_2_2_lattice3(sK0,sK1))),
% 4.57/0.96    inference(resolution,[],[f1580,f77])).
% 4.57/0.96  fof(f77,plain,(
% 4.57/0.96    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))),
% 4.57/0.96    inference(cnf_transformation,[],[f44])).
% 4.57/0.96  fof(f1580,plain,(
% 4.57/0.96    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f1563,f854])).
% 4.57/0.96  fof(f854,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f853,f70])).
% 4.57/0.96  fof(f853,plain,(
% 4.57/0.96    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f852,f71])).
% 4.57/0.96  fof(f852,plain,(
% 4.57/0.96    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f851,f72])).
% 4.57/0.96  fof(f851,plain,(
% 4.57/0.96    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f850,f73])).
% 4.57/0.96  fof(f850,plain,(
% 4.57/0.96    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(duplicate_literal_removal,[],[f847])).
% 4.57/0.96  fof(f847,plain,(
% 4.57/0.96    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~r2_hidden(X0,a_2_2_lattice3(sK0,X1))) )),
% 4.57/0.96    inference(superposition,[],[f106,f365])).
% 4.57/0.96  fof(f365,plain,(
% 4.57/0.96    ( ! [X31,X32] : (sK9(X31,sK0,X32) = X31 | ~r2_hidden(X31,a_2_2_lattice3(sK0,X32))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f364,f70])).
% 4.57/0.96  fof(f364,plain,(
% 4.57/0.96    ( ! [X31,X32] : (sK9(X31,sK0,X32) = X31 | ~r2_hidden(X31,a_2_2_lattice3(sK0,X32)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f363,f71])).
% 4.57/0.96  fof(f363,plain,(
% 4.57/0.96    ( ! [X31,X32] : (sK9(X31,sK0,X32) = X31 | ~r2_hidden(X31,a_2_2_lattice3(sK0,X32)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f307,f72])).
% 4.57/0.96  fof(f307,plain,(
% 4.57/0.96    ( ! [X31,X32] : (sK9(X31,sK0,X32) = X31 | ~r2_hidden(X31,a_2_2_lattice3(sK0,X32)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f73,f107])).
% 4.57/0.96  fof(f107,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (sK9(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f64])).
% 4.57/0.96  fof(f64,plain,(
% 4.57/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK9(X0,X1,X2),X2) & sK9(X0,X1,X2) = X0 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.57/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f62,f63])).
% 4.57/0.96  fof(f63,plain,(
% 4.57/0.96    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK9(X0,X1,X2),X2) & sK9(X0,X1,X2) = X0 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f62,plain,(
% 4.57/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.57/0.96    inference(rectify,[],[f61])).
% 4.57/0.96  fof(f61,plain,(
% 4.57/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.57/0.96    inference(nnf_transformation,[],[f38])).
% 4.57/0.96  fof(f38,plain,(
% 4.57/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.57/0.96    inference(flattening,[],[f37])).
% 4.57/0.96  fof(f37,plain,(
% 4.57/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 4.57/0.96    inference(ennf_transformation,[],[f6])).
% 4.57/0.96  fof(f6,axiom,(
% 4.57/0.96    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 4.57/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 4.57/0.96  fof(f106,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f64])).
% 4.57/0.96  fof(f1563,plain,(
% 4.57/0.96    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 4.57/0.96    inference(superposition,[],[f347,f329])).
% 4.57/0.96  fof(f329,plain,(
% 4.57/0.96    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f328,f70])).
% 4.57/0.96  fof(f328,plain,(
% 4.57/0.96    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f327,f71])).
% 4.57/0.96  fof(f327,plain,(
% 4.57/0.96    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f287,f72])).
% 4.57/0.96  fof(f287,plain,(
% 4.57/0.96    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f73,f82])).
% 4.57/0.96  fof(f82,plain,(
% 4.57/0.96    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f22])).
% 4.57/0.96  fof(f22,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(flattening,[],[f21])).
% 4.57/0.96  fof(f21,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f8])).
% 4.57/0.96  fof(f8,axiom,(
% 4.57/0.96    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 4.57/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).
% 4.57/0.96  fof(f347,plain,(
% 4.57/0.96    ( ! [X8,X7] : (r3_lattices(sK0,k16_lattice3(sK0,X7),X8) | ~r2_hidden(X8,X7) | ~m1_subset_1(X8,u1_struct_0(sK0))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f346,f70])).
% 4.57/0.96  fof(f346,plain,(
% 4.57/0.96    ( ! [X8,X7] : (r3_lattices(sK0,k16_lattice3(sK0,X7),X8) | ~r2_hidden(X8,X7) | ~m1_subset_1(X8,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f345,f71])).
% 4.57/0.96  fof(f345,plain,(
% 4.57/0.96    ( ! [X8,X7] : (r3_lattices(sK0,k16_lattice3(sK0,X7),X8) | ~r2_hidden(X8,X7) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f293,f72])).
% 4.57/0.96  fof(f293,plain,(
% 4.57/0.96    ( ! [X8,X7] : (r3_lattices(sK0,k16_lattice3(sK0,X7),X8) | ~r2_hidden(X8,X7) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f73,f88])).
% 4.57/0.96  fof(f88,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f28])).
% 4.57/0.96  fof(f28,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(flattening,[],[f27])).
% 4.57/0.96  fof(f27,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f9])).
% 4.57/0.96  fof(f9,axiom,(
% 4.57/0.96    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 4.57/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 4.57/0.96  fof(f4907,plain,(
% 4.57/0.96    ( ! [X33,X32] : (r2_hidden(k15_lattice3(sK0,X32),a_2_2_lattice3(sK0,X33)) | ~r4_lattice3(sK0,k15_lattice3(sK0,X32),X33)) )),
% 4.57/0.96    inference(forward_demodulation,[],[f4873,f4839])).
% 4.57/0.96  fof(f4873,plain,(
% 4.57/0.96    ( ! [X33,X32] : (r2_hidden(k15_lattice3(sK0,X32),a_2_2_lattice3(sK0,X33)) | ~r4_lattice3(sK0,sK7(sK0,X32),X33)) )),
% 4.57/0.96    inference(backward_demodulation,[],[f679,f4839])).
% 4.57/0.96  fof(f679,plain,(
% 4.57/0.96    ( ! [X33,X32] : (r2_hidden(sK7(sK0,X32),a_2_2_lattice3(sK0,X33)) | ~r4_lattice3(sK0,sK7(sK0,X32),X33)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f678,f70])).
% 4.57/0.96  fof(f678,plain,(
% 4.57/0.96    ( ! [X33,X32] : (r2_hidden(sK7(sK0,X32),a_2_2_lattice3(sK0,X33)) | ~r4_lattice3(sK0,sK7(sK0,X32),X33) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f677,f71])).
% 4.57/0.96  fof(f677,plain,(
% 4.57/0.96    ( ! [X33,X32] : (r2_hidden(sK7(sK0,X32),a_2_2_lattice3(sK0,X33)) | ~r4_lattice3(sK0,sK7(sK0,X32),X33) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f676,f72])).
% 4.57/0.96  fof(f676,plain,(
% 4.57/0.96    ( ! [X33,X32] : (r2_hidden(sK7(sK0,X32),a_2_2_lattice3(sK0,X33)) | ~r4_lattice3(sK0,sK7(sK0,X32),X33) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f620,f73])).
% 4.57/0.96  fof(f620,plain,(
% 4.57/0.96    ( ! [X33,X32] : (r2_hidden(sK7(sK0,X32),a_2_2_lattice3(sK0,X33)) | ~r4_lattice3(sK0,sK7(sK0,X32),X33) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f349,f118])).
% 4.57/0.96  fof(f118,plain,(
% 4.57/0.96    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.57/0.96    inference(equality_resolution,[],[f109])).
% 4.57/0.96  fof(f109,plain,(
% 4.57/0.96    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f64])).
% 4.57/0.96  fof(f6848,plain,(
% 4.57/0.96    ~r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | r2_hidden(sK3(sK8(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)),
% 4.57/0.96    inference(resolution,[],[f5686,f76])).
% 4.57/0.96  fof(f76,plain,(
% 4.57/0.96    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | r2_hidden(sK3(X3),sK2)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f44])).
% 4.57/0.96  fof(f5686,plain,(
% 4.57/0.96    m1_subset_1(sK8(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))),
% 4.57/0.96    inference(subsumption_resolution,[],[f5685,f70])).
% 4.57/0.96  fof(f5685,plain,(
% 4.57/0.96    m1_subset_1(sK8(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 4.57/0.96    inference(subsumption_resolution,[],[f5684,f73])).
% 4.57/0.96  fof(f5684,plain,(
% 4.57/0.96    m1_subset_1(sK8(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 4.57/0.96    inference(subsumption_resolution,[],[f5678,f4856])).
% 4.57/0.96  fof(f5678,plain,(
% 4.57/0.96    m1_subset_1(sK8(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 4.57/0.96    inference(resolution,[],[f5645,f101])).
% 4.57/0.96  fof(f101,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f59])).
% 4.57/0.96  fof(f9935,plain,(
% 4.57/0.96    ~r2_hidden(sK3(sK8(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)),
% 4.57/0.96    inference(subsumption_resolution,[],[f9934,f5689])).
% 4.57/0.96  fof(f9934,plain,(
% 4.57/0.96    ~r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | ~r2_hidden(sK3(sK8(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)),
% 4.57/0.96    inference(subsumption_resolution,[],[f9928,f5686])).
% 4.57/0.96  fof(f9928,plain,(
% 4.57/0.96    ~m1_subset_1(sK8(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) | ~r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),sK1) | ~r2_hidden(sK3(sK8(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)),
% 4.57/0.96    inference(resolution,[],[f9327,f579])).
% 4.57/0.96  fof(f579,plain,(
% 4.57/0.96    ( ! [X0,X1] : (r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r2_hidden(sK3(X0),X1)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f578,f74])).
% 4.57/0.96  fof(f74,plain,(
% 4.57/0.96    ( ! [X3] : (m1_subset_1(sK3(X3),u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 4.57/0.96    inference(cnf_transformation,[],[f44])).
% 4.57/0.96  fof(f578,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~r2_hidden(sK3(X0),X1) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f577,f70])).
% 4.57/0.96  fof(f577,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~r2_hidden(sK3(X0),X1) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f576,f71])).
% 4.57/0.96  fof(f576,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~r2_hidden(sK3(X0),X1) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f575,f72])).
% 4.57/0.96  fof(f575,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~r2_hidden(sK3(X0),X1) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f574,f73])).
% 4.57/0.96  fof(f574,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~r2_hidden(sK3(X0),X1) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(duplicate_literal_removal,[],[f571])).
% 4.57/0.96  fof(f571,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~r2_hidden(sK3(X0),X1) | ~m1_subset_1(sK3(X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f75,f119])).
% 4.57/0.96  fof(f119,plain,(
% 4.57/0.96    ( ! [X4,X2,X3,X1] : (r2_hidden(X3,a_2_5_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.57/0.96    inference(equality_resolution,[],[f115])).
% 4.57/0.96  fof(f115,plain,(
% 4.57/0.96    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f69])).
% 4.57/0.96  fof(f69,plain,(
% 4.57/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK11(X0,X1,X2),X2) & r3_lattices(X1,sK10(X0,X1,X2),sK11(X0,X1,X2)) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))) & sK10(X0,X1,X2) = X0 & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.57/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f66,f68,f67])).
% 4.57/0.96  fof(f67,plain,(
% 4.57/0.96    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK10(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) & sK10(X0,X1,X2) = X0 & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f68,plain,(
% 4.57/0.96    ! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,sK10(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK11(X0,X1,X2),X2) & r3_lattices(X1,sK10(X0,X1,X2),sK11(X0,X1,X2)) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))))),
% 4.57/0.96    introduced(choice_axiom,[])).
% 4.57/0.96  fof(f66,plain,(
% 4.57/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.57/0.96    inference(rectify,[],[f65])).
% 4.57/0.96  fof(f65,plain,(
% 4.57/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.57/0.96    inference(nnf_transformation,[],[f40])).
% 4.57/0.96  fof(f40,plain,(
% 4.57/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 4.57/0.96    inference(flattening,[],[f39])).
% 4.57/0.96  fof(f39,plain,(
% 4.57/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 4.57/0.96    inference(ennf_transformation,[],[f7])).
% 4.57/0.96  fof(f7,axiom,(
% 4.57/0.96    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 4.57/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).
% 4.57/0.96  fof(f75,plain,(
% 4.57/0.96    ( ! [X3] : (r3_lattices(sK0,X3,sK3(X3)) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 4.57/0.96    inference(cnf_transformation,[],[f44])).
% 4.57/0.96  fof(f9327,plain,(
% 4.57/0.96    ~r2_hidden(sK8(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2))),
% 4.57/0.96    inference(resolution,[],[f5692,f5320])).
% 4.57/0.96  fof(f5320,plain,(
% 4.57/0.96    ( ! [X0,X1] : (r1_lattices(sK0,X0,k15_lattice3(sK0,X1)) | ~r2_hidden(X0,a_2_5_lattice3(sK0,X1))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f5319,f870])).
% 4.57/0.96  fof(f870,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f869,f70])).
% 4.57/0.96  fof(f869,plain,(
% 4.57/0.96    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f868,f71])).
% 4.57/0.96  fof(f868,plain,(
% 4.57/0.96    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f867,f72])).
% 4.57/0.96  fof(f867,plain,(
% 4.57/0.96    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f866,f73])).
% 4.57/0.96  fof(f866,plain,(
% 4.57/0.96    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(duplicate_literal_removal,[],[f863])).
% 4.57/0.96  fof(f863,plain,(
% 4.57/0.96    ( ! [X0,X1] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~r2_hidden(X0,a_2_5_lattice3(sK0,X1))) )),
% 4.57/0.96    inference(superposition,[],[f110,f374])).
% 4.57/0.96  fof(f374,plain,(
% 4.57/0.96    ( ! [X37,X38] : (sK10(X37,sK0,X38) = X37 | ~r2_hidden(X37,a_2_5_lattice3(sK0,X38))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f373,f70])).
% 4.57/0.96  fof(f373,plain,(
% 4.57/0.96    ( ! [X37,X38] : (sK10(X37,sK0,X38) = X37 | ~r2_hidden(X37,a_2_5_lattice3(sK0,X38)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f372,f71])).
% 4.57/0.96  fof(f372,plain,(
% 4.57/0.96    ( ! [X37,X38] : (sK10(X37,sK0,X38) = X37 | ~r2_hidden(X37,a_2_5_lattice3(sK0,X38)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f310,f72])).
% 4.57/0.96  fof(f310,plain,(
% 4.57/0.96    ( ! [X37,X38] : (sK10(X37,sK0,X38) = X37 | ~r2_hidden(X37,a_2_5_lattice3(sK0,X38)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f73,f111])).
% 4.57/0.96  fof(f111,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (sK10(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f69])).
% 4.57/0.96  fof(f110,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f69])).
% 4.57/0.96  fof(f5319,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k15_lattice3(sK0,X1))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f5303,f4856])).
% 4.57/0.96  fof(f5303,plain,(
% 4.57/0.96    ( ! [X0,X1] : (~r2_hidden(X0,a_2_5_lattice3(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k15_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))) )),
% 4.57/0.96    inference(resolution,[],[f5059,f354])).
% 4.57/0.96  fof(f354,plain,(
% 4.57/0.96    ( ! [X17,X18,X16] : (~r4_lattice3(sK0,X17,X18) | ~r2_hidden(X16,X18) | ~m1_subset_1(X16,u1_struct_0(sK0)) | r1_lattices(sK0,X16,X17) | ~m1_subset_1(X17,u1_struct_0(sK0))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f300,f70])).
% 4.57/0.96  fof(f300,plain,(
% 4.57/0.96    ( ! [X17,X18,X16] : (r1_lattices(sK0,X16,X17) | ~r2_hidden(X16,X18) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X17,X18) | ~m1_subset_1(X17,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f73,f100])).
% 4.57/0.96  fof(f100,plain,(
% 4.57/0.96    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f59])).
% 4.57/0.96  fof(f5059,plain,(
% 4.57/0.96    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0))) )),
% 4.57/0.96    inference(superposition,[],[f4857,f332])).
% 4.57/0.96  fof(f332,plain,(
% 4.57/0.96    ( ! [X1] : (k15_lattice3(sK0,X1) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X1))) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f331,f70])).
% 4.57/0.96  fof(f331,plain,(
% 4.57/0.96    ( ! [X1] : (k15_lattice3(sK0,X1) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X1)) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f330,f71])).
% 4.57/0.96  fof(f330,plain,(
% 4.57/0.96    ( ! [X1] : (k15_lattice3(sK0,X1) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(subsumption_resolution,[],[f288,f72])).
% 4.57/0.96  fof(f288,plain,(
% 4.57/0.96    ( ! [X1] : (k15_lattice3(sK0,X1) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X1)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 4.57/0.96    inference(resolution,[],[f73,f83])).
% 4.57/0.96  fof(f83,plain,(
% 4.57/0.96    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f24])).
% 4.57/0.96  fof(f24,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 4.57/0.96    inference(flattening,[],[f23])).
% 4.57/0.96  fof(f23,plain,(
% 4.57/0.96    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 4.57/0.96    inference(ennf_transformation,[],[f11])).
% 4.57/0.96  fof(f11,axiom,(
% 4.57/0.96    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 4.57/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).
% 4.57/0.96  fof(f4857,plain,(
% 4.57/0.96    ( ! [X10] : (r4_lattice3(sK0,k15_lattice3(sK0,X10),X10)) )),
% 4.57/0.96    inference(backward_demodulation,[],[f351,f4839])).
% 4.57/0.96  fof(f5692,plain,(
% 4.57/0.96    ~r1_lattices(sK0,sK8(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))),
% 4.57/0.96    inference(subsumption_resolution,[],[f5691,f70])).
% 4.57/0.96  fof(f5691,plain,(
% 4.57/0.96    ~r1_lattices(sK0,sK8(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) | v2_struct_0(sK0)),
% 4.57/0.96    inference(subsumption_resolution,[],[f5690,f73])).
% 4.57/0.96  fof(f5690,plain,(
% 4.57/0.96    ~r1_lattices(sK0,sK8(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 4.57/0.96    inference(subsumption_resolution,[],[f5680,f4856])).
% 4.57/0.96  fof(f5680,plain,(
% 4.57/0.96    ~r1_lattices(sK0,sK8(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 4.57/0.96    inference(resolution,[],[f5645,f103])).
% 4.57/0.96  fof(f103,plain,(
% 4.57/0.96    ( ! [X2,X0,X1] : (r4_lattice3(X0,X1,X2) | ~r1_lattices(X0,sK8(X0,X1,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 4.57/0.96    inference(cnf_transformation,[],[f59])).
% 4.57/0.96  % SZS output end Proof for theBenchmark
% 4.57/0.96  % (12077)------------------------------
% 4.57/0.96  % (12077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.57/0.96  % (12077)Termination reason: Refutation
% 4.57/0.96  
% 4.57/0.96  % (12077)Memory used [KB]: 5628
% 4.57/0.96  % (12077)Time elapsed: 0.559 s
% 4.57/0.96  % (12077)------------------------------
% 4.57/0.96  % (12077)------------------------------
% 4.57/0.96  % (12053)Success in time 0.61 s
%------------------------------------------------------------------------------
