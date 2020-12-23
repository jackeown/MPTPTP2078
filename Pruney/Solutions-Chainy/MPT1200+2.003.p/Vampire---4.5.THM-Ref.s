%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 546 expanded)
%              Number of leaves         :   18 ( 248 expanded)
%              Depth                    :   11
%              Number of atoms          :  404 (4737 expanded)
%              Number of equality atoms :   59 (  64 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2018,plain,(
    $false ),
    inference(global_subsumption,[],[f641,f2017])).

fof(f2017,plain,(
    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(backward_demodulation,[],[f431,f2015])).

fof(f2015,plain,(
    k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(backward_demodulation,[],[f455,f2014])).

fof(f2014,plain,(
    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f1969,f558])).

fof(f558,plain,(
    sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f44,f46,f47,f48,f49,f52,f50,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))
    & r1_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & v7_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                    & r1_lattices(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3))
                  & r1_lattices(sK0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & v7_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3))
                & r1_lattices(sK0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,X2,X3))
              & r1_lattices(sK0,sK1,X2)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,X2,X3))
            & r1_lattices(sK0,sK1,X2)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,sK2,X3))
          & r1_lattices(sK0,sK1,sK2)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,sK2,X3))
        & r1_lattices(sK0,sK1,sK2)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))
      & r1_lattices(sK0,sK1,sK2)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v7_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattices(X0,X1,X2)
                     => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).

fof(f52,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1969,plain,(
    k2_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f44,f72,f45,f49,f50,f51,f58])).

fof(f58,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v7_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattices)).

fof(f51,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    v7_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f48,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f455,plain,(
    k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f44,f48,f46,f49,f82,f63])).

fof(f63,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f35,f37,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0))
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(f82,plain,(
    m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f72,f50,f51,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f431,plain,(
    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k2_lattices(sK0,sK1,sK3),k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f44,f48,f47,f81,f82,f67])).

fof(f67,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),sK10(X0)))
            & m1_subset_1(sK10(X0),u1_struct_0(X0))
            & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),sK10(X0)))
        & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(f81,plain,(
    m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f72,f49,f51,f71])).

fof(f641,plain,(
    k2_lattices(sK0,sK1,sK3) != k2_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f44,f46,f47,f48,f81,f53,f82,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:06:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (9807)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (9815)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.47  % (9815)Refutation not found, incomplete strategy% (9815)------------------------------
% 0.20/0.47  % (9815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9815)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (9815)Memory used [KB]: 6140
% 0.20/0.47  % (9815)Time elapsed: 0.068 s
% 0.20/0.47  % (9815)------------------------------
% 0.20/0.47  % (9815)------------------------------
% 0.20/0.50  % (9812)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (9798)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (9799)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (9796)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (9795)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (9801)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (9814)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (9809)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (9817)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (9818)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.51  % (9800)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.51  % (9811)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (9797)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.51  % (9818)Refutation not found, incomplete strategy% (9818)------------------------------
% 0.20/0.51  % (9818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9818)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9818)Memory used [KB]: 10618
% 0.20/0.51  % (9818)Time elapsed: 0.100 s
% 0.20/0.51  % (9818)------------------------------
% 0.20/0.51  % (9818)------------------------------
% 0.20/0.51  % (9811)Refutation not found, incomplete strategy% (9811)------------------------------
% 0.20/0.51  % (9811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9811)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9811)Memory used [KB]: 1663
% 0.20/0.51  % (9811)Time elapsed: 0.104 s
% 0.20/0.51  % (9811)------------------------------
% 0.20/0.51  % (9811)------------------------------
% 0.20/0.51  % (9798)Refutation not found, incomplete strategy% (9798)------------------------------
% 0.20/0.51  % (9798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9798)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9798)Memory used [KB]: 10618
% 0.20/0.51  % (9798)Time elapsed: 0.099 s
% 0.20/0.51  % (9798)------------------------------
% 0.20/0.51  % (9798)------------------------------
% 0.20/0.52  % (9805)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.52  % (9806)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.52  % (9802)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (9805)Refutation not found, incomplete strategy% (9805)------------------------------
% 0.20/0.52  % (9805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (9805)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (9805)Memory used [KB]: 10618
% 0.20/0.52  % (9805)Time elapsed: 0.113 s
% 0.20/0.52  % (9805)------------------------------
% 0.20/0.52  % (9805)------------------------------
% 0.20/0.52  % (9802)Refutation not found, incomplete strategy% (9802)------------------------------
% 0.20/0.52  % (9802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (9802)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (9802)Memory used [KB]: 6140
% 0.20/0.52  % (9802)Time elapsed: 0.114 s
% 0.20/0.52  % (9802)------------------------------
% 0.20/0.52  % (9802)------------------------------
% 0.20/0.52  % (9808)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.52  % (9803)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (9813)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.53  % (9816)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.53  % (9804)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.53  % (9810)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.54  % (9803)Refutation not found, incomplete strategy% (9803)------------------------------
% 0.20/0.54  % (9803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (9803)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (9803)Memory used [KB]: 10618
% 0.20/0.54  % (9803)Time elapsed: 0.136 s
% 0.20/0.54  % (9803)------------------------------
% 0.20/0.54  % (9803)------------------------------
% 0.20/0.56  % (9809)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 1.79/0.58  % SZS output start Proof for theBenchmark
% 1.79/0.58  fof(f2018,plain,(
% 1.79/0.58    $false),
% 1.79/0.58    inference(global_subsumption,[],[f641,f2017])).
% 1.79/0.58  fof(f2017,plain,(
% 1.79/0.58    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))),
% 1.79/0.58    inference(backward_demodulation,[],[f431,f2015])).
% 1.79/0.58  fof(f2015,plain,(
% 1.79/0.58    k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))),
% 1.79/0.58    inference(backward_demodulation,[],[f455,f2014])).
% 1.79/0.58  fof(f2014,plain,(
% 1.79/0.58    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3))),
% 1.79/0.58    inference(forward_demodulation,[],[f1969,f558])).
% 1.79/0.58  fof(f558,plain,(
% 1.79/0.58    sK1 = k2_lattices(sK0,sK1,sK2)),
% 1.79/0.58    inference(unit_resulting_resolution,[],[f44,f46,f47,f48,f49,f52,f50,f56])).
% 1.79/0.58  fof(f56,plain,(
% 1.79/0.58    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.79/0.58    inference(cnf_transformation,[],[f27])).
% 1.79/0.58  fof(f27,plain,(
% 1.79/0.58    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(nnf_transformation,[],[f13])).
% 1.79/0.58  fof(f13,plain,(
% 1.79/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(flattening,[],[f12])).
% 1.79/0.58  fof(f12,plain,(
% 1.79/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.79/0.58    inference(ennf_transformation,[],[f6])).
% 1.79/0.58  fof(f6,axiom,(
% 1.79/0.58    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.79/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 1.79/0.58  fof(f50,plain,(
% 1.79/0.58    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.79/0.58    inference(cnf_transformation,[],[f26])).
% 1.79/0.58  fof(f26,plain,(
% 1.79/0.58    (((~r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & v7_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.79/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f25,f24,f23,f22])).
% 1.79/0.58  fof(f22,plain,(
% 1.79/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & v7_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f23,plain,(
% 1.79/0.58    ? [X1] : (? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f24,plain,(
% 1.79/0.58    ? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,sK2,X3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f25,plain,(
% 1.79/0.58    ? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,sK2,X3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f10,plain,(
% 1.79/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0))),
% 1.79/0.58    inference(flattening,[],[f9])).
% 1.79/0.58  fof(f9,plain,(
% 1.79/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)))),
% 1.79/0.58    inference(ennf_transformation,[],[f8])).
% 1.79/0.58  fof(f8,negated_conjecture,(
% 1.79/0.58    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 1.79/0.58    inference(negated_conjecture,[],[f7])).
% 1.79/0.58  fof(f7,conjecture,(
% 1.79/0.58    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 1.79/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).
% 1.79/0.58  fof(f52,plain,(
% 1.79/0.58    r1_lattices(sK0,sK1,sK2)),
% 1.79/0.58    inference(cnf_transformation,[],[f26])).
% 1.79/0.58  fof(f49,plain,(
% 1.79/0.58    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.79/0.58    inference(cnf_transformation,[],[f26])).
% 1.79/0.58  fof(f48,plain,(
% 1.79/0.58    l3_lattices(sK0)),
% 1.79/0.58    inference(cnf_transformation,[],[f26])).
% 1.79/0.58  fof(f47,plain,(
% 1.79/0.58    v9_lattices(sK0)),
% 1.79/0.58    inference(cnf_transformation,[],[f26])).
% 1.79/0.58  fof(f46,plain,(
% 1.79/0.58    v8_lattices(sK0)),
% 1.79/0.58    inference(cnf_transformation,[],[f26])).
% 1.79/0.58  fof(f44,plain,(
% 1.79/0.58    ~v2_struct_0(sK0)),
% 1.79/0.58    inference(cnf_transformation,[],[f26])).
% 1.79/0.58  fof(f1969,plain,(
% 1.79/0.58    k2_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3))),
% 1.79/0.58    inference(unit_resulting_resolution,[],[f44,f72,f45,f49,f50,f51,f58])).
% 1.79/0.58  fof(f58,plain,(
% 1.79/0.58    ( ! [X6,X4,X0,X5] : (~v7_lattices(X0) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.79/0.58    inference(cnf_transformation,[],[f33])).
% 1.79/0.58  fof(f33,plain,(
% 1.79/0.58    ! [X0] : (((v7_lattices(X0) | (((k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 1.79/0.58  fof(f30,plain,(
% 1.79/0.58    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f31,plain,(
% 1.79/0.58    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f32,plain,(
% 1.79/0.58    ! [X0] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f29,plain,(
% 1.79/0.58    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(rectify,[],[f28])).
% 1.79/0.58  fof(f28,plain,(
% 1.79/0.58    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(nnf_transformation,[],[f15])).
% 1.79/0.58  fof(f15,plain,(
% 1.79/0.58    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(flattening,[],[f14])).
% 1.79/0.58  fof(f14,plain,(
% 1.79/0.58    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.79/0.58    inference(ennf_transformation,[],[f1])).
% 1.79/0.58  fof(f1,axiom,(
% 1.79/0.58    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3))))))),
% 1.79/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattices)).
% 1.79/0.58  fof(f51,plain,(
% 1.79/0.58    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.79/0.58    inference(cnf_transformation,[],[f26])).
% 1.79/0.58  fof(f45,plain,(
% 1.79/0.58    v7_lattices(sK0)),
% 1.79/0.58    inference(cnf_transformation,[],[f26])).
% 1.79/0.58  fof(f72,plain,(
% 1.79/0.58    l1_lattices(sK0)),
% 1.79/0.58    inference(unit_resulting_resolution,[],[f48,f54])).
% 1.79/0.58  fof(f54,plain,(
% 1.79/0.58    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 1.79/0.58    inference(cnf_transformation,[],[f11])).
% 1.79/0.58  fof(f11,plain,(
% 1.79/0.58    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.79/0.58    inference(ennf_transformation,[],[f5])).
% 1.79/0.58  fof(f5,axiom,(
% 1.79/0.58    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.79/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.79/0.58  fof(f455,plain,(
% 1.79/0.58    k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK2,sK3))),
% 1.79/0.58    inference(unit_resulting_resolution,[],[f44,f48,f46,f49,f82,f63])).
% 1.79/0.58  fof(f63,plain,(
% 1.79/0.58    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.79/0.58    inference(cnf_transformation,[],[f38])).
% 1.79/0.58  fof(f38,plain,(
% 1.79/0.58    ! [X0] : (((v8_lattices(X0) | ((sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0)) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f35,f37,f36])).
% 1.79/0.58  fof(f36,plain,(
% 1.79/0.58    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f37,plain,(
% 1.79/0.58    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0)) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f35,plain,(
% 1.79/0.58    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(rectify,[],[f34])).
% 1.79/0.58  fof(f34,plain,(
% 1.79/0.58    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(nnf_transformation,[],[f17])).
% 1.79/0.58  fof(f17,plain,(
% 1.79/0.58    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(flattening,[],[f16])).
% 1.79/0.58  fof(f16,plain,(
% 1.79/0.58    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.79/0.58    inference(ennf_transformation,[],[f2])).
% 1.79/0.58  fof(f2,axiom,(
% 1.79/0.58    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 1.79/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 1.79/0.58  fof(f82,plain,(
% 1.79/0.58    m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))),
% 1.79/0.58    inference(unit_resulting_resolution,[],[f44,f72,f50,f51,f71])).
% 1.79/0.58  fof(f71,plain,(
% 1.79/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 1.79/0.58    inference(cnf_transformation,[],[f21])).
% 1.79/0.58  fof(f21,plain,(
% 1.79/0.58    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(flattening,[],[f20])).
% 1.79/0.58  fof(f20,plain,(
% 1.79/0.58    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 1.79/0.58    inference(ennf_transformation,[],[f4])).
% 1.79/0.58  fof(f4,axiom,(
% 1.79/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 1.79/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).
% 1.79/0.58  fof(f431,plain,(
% 1.79/0.58    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,k2_lattices(sK0,sK1,sK3),k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)))),
% 1.79/0.58    inference(unit_resulting_resolution,[],[f44,f48,f47,f81,f82,f67])).
% 1.79/0.58  fof(f67,plain,(
% 1.79/0.58    ( ! [X4,X0,X3] : (~v9_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.79/0.58    inference(cnf_transformation,[],[f43])).
% 1.79/0.58  fof(f43,plain,(
% 1.79/0.58    ! [X0] : (((v9_lattices(X0) | ((sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),sK10(X0))) & m1_subset_1(sK10(X0),u1_struct_0(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f40,f42,f41])).
% 1.79/0.58  fof(f41,plain,(
% 1.79/0.58    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f42,plain,(
% 1.79/0.58    ! [X0] : (? [X2] : (sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),sK10(X0))) & m1_subset_1(sK10(X0),u1_struct_0(X0))))),
% 1.79/0.58    introduced(choice_axiom,[])).
% 1.79/0.58  fof(f40,plain,(
% 1.79/0.58    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(rectify,[],[f39])).
% 1.79/0.58  fof(f39,plain,(
% 1.79/0.58    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(nnf_transformation,[],[f19])).
% 1.79/0.58  fof(f19,plain,(
% 1.79/0.58    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.79/0.58    inference(flattening,[],[f18])).
% 1.79/0.58  fof(f18,plain,(
% 1.79/0.58    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.79/0.58    inference(ennf_transformation,[],[f3])).
% 1.79/0.58  fof(f3,axiom,(
% 1.79/0.58    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 1.79/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 1.79/0.58  fof(f81,plain,(
% 1.79/0.58    m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0))),
% 1.79/0.58    inference(unit_resulting_resolution,[],[f44,f72,f49,f51,f71])).
% 1.79/0.58  fof(f641,plain,(
% 1.79/0.58    k2_lattices(sK0,sK1,sK3) != k2_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))),
% 1.79/0.58    inference(unit_resulting_resolution,[],[f44,f46,f47,f48,f81,f53,f82,f57])).
% 1.79/0.58  fof(f57,plain,(
% 1.79/0.58    ( ! [X2,X0,X1] : (~v9_lattices(X0) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.79/0.58    inference(cnf_transformation,[],[f27])).
% 1.79/0.58  fof(f53,plain,(
% 1.79/0.58    ~r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))),
% 1.79/0.58    inference(cnf_transformation,[],[f26])).
% 1.79/0.58  % SZS output end Proof for theBenchmark
% 1.79/0.58  % (9809)------------------------------
% 1.79/0.58  % (9809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.58  % (9809)Termination reason: Refutation
% 1.79/0.58  
% 1.79/0.58  % (9809)Memory used [KB]: 12920
% 1.79/0.58  % (9809)Time elapsed: 0.137 s
% 1.79/0.58  % (9809)------------------------------
% 1.79/0.58  % (9809)------------------------------
% 1.79/0.58  % (9794)Success in time 0.232 s
%------------------------------------------------------------------------------
