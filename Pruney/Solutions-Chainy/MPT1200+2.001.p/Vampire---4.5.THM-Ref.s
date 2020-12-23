%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 436 expanded)
%              Number of leaves         :   18 ( 196 expanded)
%              Depth                    :   11
%              Number of atoms          :  395 (3725 expanded)
%              Number of equality atoms :   59 (  64 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2167,plain,(
    $false ),
    inference(global_subsumption,[],[f189,f2165])).

fof(f2165,plain,(
    k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(backward_demodulation,[],[f376,f2164])).

fof(f2164,plain,(
    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)) ),
    inference(forward_demodulation,[],[f2119,f617])).

fof(f617,plain,(
    sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f591,f93])).

fof(f93,plain,(
    sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f44,f74,f49,f52,f50,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f74,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f48,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f48,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f591,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f44,f48,f47,f49,f50,f67])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f47,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f2119,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f376,plain,(
    k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f44,f48,f46,f49,f83,f63])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f83,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f46,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f189,plain,(
    k2_lattices(sK0,sK2,sK3) != k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f44,f74,f82,f53,f83,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f72,f49,f51,f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:52:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (11727)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.46  % (11735)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.47  % (11735)Refutation not found, incomplete strategy% (11735)------------------------------
% 0.20/0.47  % (11735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (11735)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (11735)Memory used [KB]: 10618
% 0.20/0.48  % (11735)Time elapsed: 0.067 s
% 0.20/0.48  % (11735)------------------------------
% 0.20/0.48  % (11735)------------------------------
% 0.20/0.48  % (11734)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.48  % (11716)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (11721)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.49  % (11717)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (11733)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (11723)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.50  % (11718)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (11719)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (11712)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (11732)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.50  % (11729)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (11713)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (11726)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (11722)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  % (11724)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (11725)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  % (11720)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.52  % (11714)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.52  % (11731)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.52  % (11715)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.52  % (11715)Refutation not found, incomplete strategy% (11715)------------------------------
% 0.20/0.52  % (11715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11715)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11715)Memory used [KB]: 10618
% 0.20/0.52  % (11715)Time elapsed: 0.122 s
% 0.20/0.52  % (11715)------------------------------
% 0.20/0.52  % (11715)------------------------------
% 0.20/0.52  % (11730)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.52  % (11722)Refutation not found, incomplete strategy% (11722)------------------------------
% 0.20/0.52  % (11722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11722)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11722)Memory used [KB]: 10746
% 0.20/0.52  % (11722)Time elapsed: 0.105 s
% 0.20/0.52  % (11722)------------------------------
% 0.20/0.52  % (11722)------------------------------
% 0.20/0.53  % (11728)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.54  % (11720)Refutation not found, incomplete strategy% (11720)------------------------------
% 0.20/0.54  % (11720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11720)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11720)Memory used [KB]: 10746
% 0.20/0.54  % (11720)Time elapsed: 0.117 s
% 0.20/0.54  % (11720)------------------------------
% 0.20/0.54  % (11720)------------------------------
% 0.20/0.57  % (11726)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f2167,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(global_subsumption,[],[f189,f2165])).
% 0.20/0.57  fof(f2165,plain,(
% 0.20/0.57    k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))),
% 0.20/0.57    inference(backward_demodulation,[],[f376,f2164])).
% 0.20/0.57  fof(f2164,plain,(
% 0.20/0.57    k2_lattices(sK0,sK1,sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3))),
% 0.20/0.57    inference(forward_demodulation,[],[f2119,f617])).
% 0.20/0.57  fof(f617,plain,(
% 0.20/0.57    sK1 = k2_lattices(sK0,sK1,sK2)),
% 0.20/0.57    inference(forward_demodulation,[],[f591,f93])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f44,f74,f49,f52,f50,f56])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | v2_struct_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(flattening,[],[f12])).
% 0.20/0.57  fof(f12,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    (((~r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & v7_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f25,f24,f23,f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v9_lattices(sK0) & v8_lattices(sK0) & v7_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ? [X1] : (? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,X1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ? [X2] : (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,X2,X3)) & r1_lattices(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,sK2,X3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ? [X3] : (~r1_lattices(sK0,k2_lattices(sK0,sK1,X3),k2_lattices(sK0,sK2,X3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3)) & r1_lattices(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f10,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.57    inference(flattening,[],[f9])).
% 0.20/0.57  fof(f9,plain,(
% 0.20/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) & r1_lattices(X0,X1,X2)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,negated_conjecture,(
% 0.20/0.57    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 0.20/0.57    inference(negated_conjecture,[],[f7])).
% 0.20/0.57  fof(f7,conjecture,(
% 0.20/0.57    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)))))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_lattices)).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    r1_lattices(sK0,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f74,plain,(
% 0.20/0.57    l2_lattices(sK0)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f48,f55])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,plain,(
% 0.20/0.57    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    l3_lattices(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ~v2_struct_0(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f591,plain,(
% 0.20/0.57    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f44,f48,f47,f49,f50,f67])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X4,X0,X3] : (~v9_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X0] : (((v9_lattices(X0) | ((sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),sK10(X0))) & m1_subset_1(sK10(X0),u1_struct_0(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f40,f42,f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0] : (? [X2] : (sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),sK10(X0))) & m1_subset_1(sK10(X0),u1_struct_0(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(rectify,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(flattening,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    v9_lattices(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f2119,plain,(
% 0.20/0.57    k2_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK3) = k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f44,f72,f45,f49,f50,f51,f58])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X6,X4,X0,X5] : (~v7_lattices(X0) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0] : (((v7_lattices(X0) | (((k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(rectify,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(flattening,[],[f14])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3))))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattices)).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    v7_lattices(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    l1_lattices(sK0)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f48,f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f376,plain,(
% 0.20/0.57    k2_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k2_lattices(sK0,sK1,k2_lattices(sK0,sK2,sK3)),k2_lattices(sK0,sK2,sK3))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f44,f48,f46,f49,f83,f63])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X0] : (((v8_lattices(X0) | ((sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0)) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f35,f37,f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK8(X0) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),sK8(X0)) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(rectify,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(flattening,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    m1_subset_1(k2_lattices(sK0,sK2,sK3),u1_struct_0(sK0))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f44,f72,f50,f51,f71])).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.57    inference(flattening,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    v8_lattices(sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f189,plain,(
% 0.20/0.57    k2_lattices(sK0,sK2,sK3) != k1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f44,f74,f82,f53,f83,f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~l2_lattices(X0) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ~r1_lattices(sK0,k2_lattices(sK0,sK1,sK3),k2_lattices(sK0,sK2,sK3))),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f82,plain,(
% 0.20/0.57    m1_subset_1(k2_lattices(sK0,sK1,sK3),u1_struct_0(sK0))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f44,f72,f49,f51,f71])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (11726)------------------------------
% 0.20/0.57  % (11726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (11726)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (11726)Memory used [KB]: 13048
% 0.20/0.57  % (11726)Time elapsed: 0.112 s
% 0.20/0.57  % (11726)------------------------------
% 0.20/0.57  % (11726)------------------------------
% 1.76/0.57  % (11711)Success in time 0.224 s
%------------------------------------------------------------------------------
