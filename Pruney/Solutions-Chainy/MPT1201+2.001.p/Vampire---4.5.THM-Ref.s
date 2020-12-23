%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:37 EST 2020

% Result     : Theorem 13.73s
% Output     : Refutation 14.18s
% Verified   : 
% Statistics : Number of formulae       : 1312 (1139820 expanded)
%              Number of leaves         :   30 (329293 expanded)
%              Depth                    :   53
%              Number of atoms          : 1928 (8580955 expanded)
%              Number of equality atoms : 1287 (1092135 expanded)
%              Maximal formula depth    :   12 (   2 average)
%              Maximal term depth       :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65061,plain,(
    $false ),
    inference(global_subsumption,[],[f4809,f65060])).

fof(f65060,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f52601,f64896])).

fof(f64896,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f19115,f64890])).

fof(f64890,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f47629,f64693])).

fof(f64693,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(backward_demodulation,[],[f5733,f64686])).

fof(f64686,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f55433,f64597])).

fof(f64597,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(backward_demodulation,[],[f19106,f64592])).

fof(f64592,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f51385,f64591])).

fof(f64591,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f64590,f10682])).

fof(f10682,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f10510,f10679])).

fof(f10679,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f10530,f10678])).

fof(f10678,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f10474,f8286])).

fof(f8286,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f8285,f3774])).

fof(f3774,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f134,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f134,plain,(
    m1_subset_1(sK9(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f81,f83,f108])).

fof(f108,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),u1_struct_0(X0))
      | v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0)))
            & m1_subset_1(sK9(X0),u1_struct_0(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f64,f67,f66,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3))
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3))
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3))
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0)))
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6))
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v11_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v11_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).

fof(f83,plain,(
    ~ v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ v11_lattices(sK0)
    & ! [X1] :
        ( ! [X2] :
            ( ! [X3] :
                ( k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,X1))
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ~ v11_lattices(X0)
        & ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) = k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ~ v11_lattices(sK0)
      & ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,X1))
                  | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
              | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ~ v11_lattices(X0)
      & ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) = k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ~ v11_lattices(X0)
      & ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) = k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) = k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) ) ) )
         => v11_lattices(X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) = k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) ) ) )
       => v11_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_lattices)).

fof(f81,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f132,plain,(
    m1_subset_1(sK7(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f81,f83,f106])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),u1_struct_0(X0))
      | v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f124,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f81,f84])).

fof(f84,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f128,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f81,f79,f80,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f80,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f8285,plain,(
    k2_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f8284,f4475])).

fof(f4475,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) ),
    inference(backward_demodulation,[],[f3767,f4115])).

fof(f4115,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f134,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f186,plain,(
    m1_subset_1(k3_lattices(sK0,sK7(sK0),sK8(sK0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f133,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattices)).

fof(f133,plain,(
    m1_subset_1(sK8(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f81,f83,f107])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(X0),u1_struct_0(X0))
      | v11_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f125,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f81,f85])).

fof(f85,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f126,plain,(
    v4_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f81,f79,f80,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3767,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f134,f122])).

fof(f8284,plain,(
    k2_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) ),
    inference(forward_demodulation,[],[f8056,f3144])).

fof(f3144,plain,(
    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f424,f2833])).

fof(f2833,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,sK7(sK0),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f133,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f424,plain,(
    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f133,f110])).

fof(f110,plain,(
    ! [X4,X0,X3] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),sK11(X0)))
            & m1_subset_1(sK11(X0),u1_struct_0(X0))
            & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f70,f72,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),sK11(X0)))
        & m1_subset_1(sK11(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
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
    inference(rectify,[],[f69])).

fof(f69,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f131,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f81,f79,f80,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8056,plain,(
    k2_lattices(sK0,sK7(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f132,f186,f134,f98])).

fof(f98,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_lattices(X0)
      | k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f58,f61,f60,f59])).

fof(f59,plain,(
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

fof(f60,plain,(
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

fof(f61,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_lattices)).

fof(f129,plain,(
    v7_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f81,f79,f80,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10474,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f310,f114])).

fof(f114,plain,(
    ! [X4,X0,X3] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK13(X0) != k1_lattices(X0,k2_lattices(X0,sK12(X0),sK13(X0)),sK13(X0))
            & m1_subset_1(sK13(X0),u1_struct_0(X0))
            & m1_subset_1(sK12(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f75,f77,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK12(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK12(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK12(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK13(X0) != k1_lattices(X0,k2_lattices(X0,sK12(X0),sK13(X0)),sK13(X0))
        & m1_subset_1(sK13(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
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
    inference(rectify,[],[f74])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f310,plain,(
    m1_subset_1(k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f186,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f130,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f81,f79,f80,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10530,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f310,f120])).

fof(f202,plain,(
    m1_subset_1(k4_lattices(sK0,sK7(sK0),sK9(sK0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f134,f121])).

fof(f10510,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f310,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f64590,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f64589,f4115])).

fof(f64589,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f64588,f18957])).

fof(f18957,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f18928,f8670])).

fof(f8670,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8669,f4389])).

fof(f4389,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK9(sK0),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3752,f4122])).

fof(f4122,plain,(
    k4_lattices(sK0,sK9(sK0),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f134,f123])).

fof(f3752,plain,(
    k4_lattices(sK0,sK9(sK0),sK7(sK0)) = k2_lattices(sK0,sK9(sK0),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f132,f122])).

fof(f8669,plain,(
    k2_lattices(sK0,sK9(sK0),sK7(sK0)) = k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8668,f4677])).

fof(f4677,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3742,f4090])).

fof(f4090,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f132,f123])).

fof(f190,plain,(
    m1_subset_1(k3_lattices(sK0,sK8(sK0),sK9(sK0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f134,f118])).

fof(f3742,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f132,f122])).

fof(f8668,plain,(
    k2_lattices(sK0,sK9(sK0),sK7(sK0)) = k2_lattices(sK0,sK9(sK0),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) ),
    inference(forward_demodulation,[],[f7887,f3014])).

fof(f3014,plain,(
    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f426,f3013])).

fof(f3013,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK9(sK0),sK8(sK0)) ),
    inference(forward_demodulation,[],[f2835,f2006])).

fof(f2006,plain,(
    k3_lattices(sK0,sK9(sK0),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f134,f119])).

fof(f2835,plain,(
    k3_lattices(sK0,sK9(sK0),sK8(sK0)) = k1_lattices(sK0,sK9(sK0),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f133,f120])).

fof(f426,plain,(
    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k1_lattices(sK0,sK9(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f133,f110])).

fof(f7887,plain,(
    k2_lattices(sK0,sK9(sK0),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f134,f190,f132,f98])).

fof(f18928,plain,(
    k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f642,f122])).

fof(f642,plain,(
    m1_subset_1(k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f190,f121])).

fof(f64588,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f64587,f18978])).

fof(f18978,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f18944,f18977])).

fof(f18977,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f18918,f8688])).

fof(f8688,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8687,f4677])).

fof(f8687,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) ),
    inference(forward_demodulation,[],[f8686,f8664])).

fof(f8664,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f8663,f4677])).

fof(f8663,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f8662,f4674])).

fof(f4674,plain,(
    sK7(sK0) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3743,f4672])).

fof(f4672,plain,(
    sK7(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) ),
    inference(forward_demodulation,[],[f4091,f3938])).

fof(f3938,plain,(
    sK7(sK0) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f3666,f3144])).

fof(f3666,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f186,f122])).

fof(f4091,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f132,f123])).

fof(f3743,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f132,f122])).

fof(f8662,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f7889,f4779])).

fof(f4779,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3658,f4006])).

fof(f4006,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f186,f123])).

fof(f3658,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f186,f122])).

fof(f7889,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f186,f132,f98])).

fof(f8686,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f7881,f3647])).

fof(f3647,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f190,f122])).

fof(f7881,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f186,f190,f132,f98])).

fof(f18918,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f642,f122])).

fof(f18944,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f642,f123])).

fof(f64587,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f64586,f55378])).

fof(f55378,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f51352,f55370])).

fof(f55370,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f53824,f55333])).

fof(f55333,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f50756,f55295])).

fof(f55295,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f55294,f52593])).

fof(f52593,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f50198,f52539])).

fof(f52539,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f50202,f52538])).

fof(f52538,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f52537,f1929])).

fof(f1929,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f202,f119])).

fof(f199,plain,(
    m1_subset_1(k4_lattices(sK0,sK7(sK0),sK8(sK0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f133,f121])).

fof(f52537,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f52536,f38688])).

fof(f38688,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f38476,f8179])).

fof(f8179,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3876,f8176])).

fof(f8176,plain,(
    k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f8175,f8140])).

fof(f8140,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f8139,f3738])).

fof(f3738,plain,(
    k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f203,f122])).

fof(f203,plain,(
    m1_subset_1(k4_lattices(sK0,sK8(sK0),sK9(sK0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f134,f121])).

fof(f8139,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f8138,f3775])).

fof(f3775,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f134,f122])).

fof(f8138,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),k2_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f8101,f3762])).

fof(f3762,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,sK7(sK0),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f133,f122])).

fof(f8101,plain,(
    k2_lattices(sK0,sK7(sK0),k2_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f132,f133,f134,f98])).

fof(f8175,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f8174,f3727])).

fof(f3727,plain,(
    k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f202,f122])).

fof(f8174,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f8173,f3774])).

fof(f8173,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f8093,f4568])).

fof(f4568,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,sK8(sK0),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3751,f4110])).

fof(f4110,plain,(
    k4_lattices(sK0,sK8(sK0),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f133,f123])).

fof(f3751,plain,(
    k4_lattices(sK0,sK8(sK0),sK7(sK0)) = k2_lattices(sK0,sK8(sK0),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f132,f122])).

fof(f8093,plain,(
    k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK8(sK0),sK7(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f133,f132,f134,f98])).

fof(f3876,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f1456,f3727])).

fof(f1456,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f202,f114])).

fof(f38476,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f1676,f120])).

fof(f1676,plain,(
    m1_subset_1(k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f203,f121])).

fof(f52536,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f52535,f8145])).

fof(f8145,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f4118,f8141])).

fof(f8141,plain,(
    k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f4467,f8140])).

fof(f4467,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3770,f4118])).

fof(f3770,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f134,f122])).

fof(f4118,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f134,f123])).

fof(f52535,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f52534,f4122])).

fof(f52534,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f52533,f4664])).

fof(f4664,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f4094,f4624])).

fof(f4624,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3746,f4621])).

fof(f4621,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3309,f4618])).

fof(f4618,plain,(
    sK7(sK0) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3308,f4571])).

fof(f4571,plain,(
    sK7(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3843,f4110])).

fof(f3843,plain,(
    sK7(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK7(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f956,f3751])).

fof(f956,plain,(
    sK7(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),sK7(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f132,f114])).

fof(f3308,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f2814,f1965])).

fof(f1965,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f132,f119])).

fof(f2814,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f132,f120])).

fof(f3309,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f1136,f3308])).

fof(f1136,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f199,f110])).

fof(f3746,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f132,f122])).

fof(f4094,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f132,f123])).

fof(f52533,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f52532,f23066])).

fof(f23066,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f22863,f23061])).

fof(f23061,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f22890,f23060])).

fof(f23060,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f22661,f6084])).

fof(f6084,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f6083,f5644])).

fof(f5644,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5643,f2848])).

fof(f2848,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,sK7(sK0),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f134,f120])).

fof(f5643,plain,(
    k1_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5517,f4571])).

fof(f5517,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f132,f134,f93])).

fof(f93,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_lattices(X0)
      | k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ( k1_lattices(X0,sK1(X0),k1_lattices(X0,sK2(X0),sK3(X0))) != k1_lattices(X0,k1_lattices(X0,sK1(X0),sK2(X0)),sK3(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f52,f55,f54,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,sK1(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK1(X0),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,sK1(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK1(X0),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,sK1(X0),k1_lattices(X0,sK2(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK1(X0),sK2(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k1_lattices(X0,sK1(X0),k1_lattices(X0,sK2(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK1(X0),sK2(X0)),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,sK1(X0),k1_lattices(X0,sK2(X0),sK3(X0))) != k1_lattices(X0,k1_lattices(X0,sK1(X0),sK2(X0)),sK3(X0))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattices)).

fof(f127,plain,(
    v5_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f81,f79,f80,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6083,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f6082,f3171])).

fof(f3171,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,sK9(sK0),sK7(sK0)) ),
    inference(forward_demodulation,[],[f2820,f2005])).

fof(f2005,plain,(
    k3_lattices(sK0,sK9(sK0),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f134,f119])).

fof(f2820,plain,(
    k3_lattices(sK0,sK9(sK0),sK7(sK0)) = k1_lattices(sK0,sK9(sK0),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f132,f120])).

fof(f6082,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f5373,f2995])).

fof(f2995,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f2844,f2001])).

fof(f2001,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f134,f119])).

fof(f2844,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f134,f120])).

fof(f5373,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f134,f132,f93])).

fof(f22661,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f1213,f110])).

fof(f1213,plain,(
    m1_subset_1(k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f199,f118])).

fof(f22890,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f22821,f22863])).

fof(f22821,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f1213,f122])).

fof(f189,plain,(
    m1_subset_1(k3_lattices(sK0,sK7(sK0),sK9(sK0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f134,f118])).

fof(f22863,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f1213,f123])).

fof(f52532,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f52531,f2001])).

fof(f52531,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f52530,f2005])).

fof(f52530,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK7(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f46573,f4618])).

fof(f46573,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK7(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f199,f134,f132,f82])).

fof(f82,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,X1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50202,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f22871,f50199])).

fof(f50199,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f47596,f50198])).

fof(f47596,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47595,f4624])).

fof(f47595,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47594,f8141])).

fof(f47594,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f47593,f3966])).

fof(f3966,plain,(
    sK7(sK0) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f3642,f2986])).

fof(f2986,plain,(
    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f432,f2848])).

fof(f432,plain,(
    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f134,f110])).

fof(f3642,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f189,f122])).

fof(f47593,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f47117,f4622])).

fof(f4622,plain,(
    sK7(sK0) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f1965,f4618])).

fof(f47117,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f199,f132,f134,f82])).

fof(f22871,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f1213,f123])).

fof(f50198,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50197,f1929])).

fof(f50197,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50196,f4451])).

fof(f4451,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3748,f4448])).

fof(f4448,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3305,f4445])).

fof(f4445,plain,(
    sK7(sK0) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3304,f4394])).

fof(f4394,plain,(
    sK7(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3835,f4122])).

fof(f3835,plain,(
    sK7(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),sK7(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f957,f3752])).

fof(f957,plain,(
    sK7(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),sK7(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f132,f114])).

fof(f3304,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2816,f1967])).

fof(f1967,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f132,f119])).

fof(f2816,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f132,f120])).

fof(f3305,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f1404,f3304])).

fof(f1404,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f202,f110])).

fof(f3748,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f132,f122])).

fof(f50196,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50195,f8176])).

fof(f50195,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50194,f3938])).

fof(f50194,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f46829,f4449])).

fof(f4449,plain,(
    sK7(sK0) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f1967,f4445])).

fof(f46829,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f202,f132,f133,f82])).

fof(f55294,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f55293,f52542])).

fof(f52542,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(backward_demodulation,[],[f27421,f52539])).

fof(f27421,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f1490,f123])).

fof(f1490,plain,(
    m1_subset_1(k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f202,f118])).

fof(f55293,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f55292,f27594])).

fof(f27594,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f27386,f27593])).

fof(f27593,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f27206,f5999])).

fof(f5999,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f5998,f3149])).

fof(f3149,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2831,f1985])).

fof(f1985,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f133,f119])).

fof(f2831,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f133,f120])).

fof(f5998,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) ),
    inference(forward_demodulation,[],[f5997,f5981])).

fof(f5981,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5980,f3149])).

fof(f5980,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5979,f4235])).

fof(f4235,plain,(
    sK8(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(backward_demodulation,[],[f3807,f4123])).

fof(f4123,plain,(
    k4_lattices(sK0,sK9(sK0),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f134,f123])).

fof(f3807,plain,(
    sK8(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(backward_demodulation,[],[f970,f3764])).

fof(f3764,plain,(
    k4_lattices(sK0,sK9(sK0),sK8(sK0)) = k2_lattices(sK0,sK9(sK0),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f133,f122])).

fof(f970,plain,(
    sK8(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f133,f114])).

fof(f5979,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5416,f2801])).

fof(f2801,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f203,f120])).

fof(f5416,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f203,f133,f93])).

fof(f5997,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5408,f3347])).

fof(f3347,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2787,f1949])).

fof(f1949,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f203,f119])).

fof(f2787,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f202,f120])).

fof(f5408,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f202,f133,f93])).

fof(f27206,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f203,f1490,f110])).

fof(f27386,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f1490,f122])).

fof(f55292,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f55291,f32858])).

fof(f32858,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f32669,f32857])).

fof(f32857,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f32408,f5967])).

fof(f5967,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(backward_demodulation,[],[f5913,f5959])).

fof(f5959,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5958,f2833])).

fof(f5958,plain,(
    k1_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5957,f4235])).

fof(f5957,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))) ),
    inference(forward_demodulation,[],[f5956,f5913])).

fof(f5956,plain,(
    k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5419,f2803])).

fof(f2803,plain,(
    k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f203,f120])).

fof(f5419,plain,(
    k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f132,f203,f133,f93])).

fof(f5913,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5912,f3571])).

fof(f3571,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2652,f1939])).

fof(f1939,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f203,f119])).

fof(f2652,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f186,f120])).

fof(f5912,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5911,f2833])).

fof(f5911,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5435,f3302])).

fof(f3302,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2817,f1968])).

fof(f1968,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f132,f119])).

fof(f2817,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f132,f120])).

fof(f5435,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f132,f133,f93])).

fof(f32408,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f1640,f110])).

fof(f1640,plain,(
    m1_subset_1(k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f203,f118])).

fof(f32669,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32590,f32638])).

fof(f32638,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f1640,f123])).

fof(f32590,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f1640,f122])).

fof(f55291,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f55290,f27476])).

fof(f27476,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f27316,f6112])).

fof(f6112,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f6111,f5915])).

fof(f5915,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f5914,f2833])).

fof(f5914,plain,(
    k1_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f5434,f4394])).

fof(f5434,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f132,f133,f93])).

fof(f6111,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f6110,f3175])).

fof(f3175,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,sK8(sK0),sK7(sK0)) ),
    inference(forward_demodulation,[],[f2819,f1987])).

fof(f1987,plain,(
    k3_lattices(sK0,sK8(sK0),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f133,f119])).

fof(f2819,plain,(
    k3_lattices(sK0,sK8(sK0),sK7(sK0)) = k1_lattices(sK0,sK8(sK0),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f132,f120])).

fof(f6110,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f5362,f3149])).

fof(f5362,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f133,f132,f93])).

fof(f27316,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f1490,f120])).

fof(f55290,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f46241,f27467])).

fof(f27467,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f27326,f5999])).

fof(f27326,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f1490,f120])).

fof(f46241,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f1490,f132,f203,f82])).

fof(f50756,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f50737,f50755])).

fof(f50755,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50754,f38701])).

fof(f38701,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f38459,f38688])).

fof(f38459,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f1676,f119])).

fof(f50754,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50753,f23040])).

fof(f23040,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f22865,f23035])).

fof(f23035,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f22837,f23034])).

fof(f23034,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f22669,f5767])).

fof(f5767,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f5703,f5766])).

fof(f5766,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5765,f2995])).

fof(f5765,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5764,f3788])).

fof(f3788,plain,(
    sK9(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(backward_demodulation,[],[f981,f3774])).

fof(f981,plain,(
    sK9(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f134,f114])).

fof(f5764,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5490,f2784])).

fof(f2784,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f202,f120])).

fof(f5490,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f202,f134,f93])).

fof(f5703,plain,(
    k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f5702,f2995])).

fof(f5702,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5506,f3385])).

fof(f3385,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2756,f1929])).

fof(f2756,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f199,f120])).

fof(f5506,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f199,f134,f93])).

fof(f22669,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f202,f1213,f110])).

fof(f22837,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f1213,f122])).

fof(f22865,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f1213,f123])).

fof(f50753,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50752,f8180])).

fof(f8180,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f4108,f8176])).

fof(f4108,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f133,f123])).

fof(f50752,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50751,f49791])).

fof(f49791,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f22872,f49790])).

fof(f49790,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f49789,f1947])).

fof(f1947,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f203,f119])).

fof(f49789,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f49788,f38687])).

fof(f38687,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f38477,f3865])).

fof(f3865,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f1604,f3738])).

fof(f1604,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f203,f114])).

fof(f38477,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f1676,f120])).

fof(f49788,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f49787,f8145])).

fof(f49787,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f49786,f4123])).

fof(f49786,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f49785,f4638])).

fof(f4638,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f4106,f3828])).

fof(f3828,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(forward_demodulation,[],[f3758,f3820])).

fof(f3820,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(backward_demodulation,[],[f3154,f3817])).

fof(f3817,plain,(
    sK8(sK0) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3153,f3816])).

fof(f3816,plain,(
    sK8(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(backward_demodulation,[],[f968,f3762])).

fof(f968,plain,(
    sK8(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f133,f114])).

fof(f3153,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f2829,f1983])).

fof(f1983,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f133,f119])).

fof(f2829,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f133,f120])).

fof(f3154,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f1137,f3153])).

fof(f1137,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f199,f110])).

fof(f3758,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f133,f122])).

fof(f4106,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f133,f123])).

fof(f49785,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f49784,f23059])).

fof(f23059,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f22864,f23054])).

fof(f23054,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f22889,f23053])).

fof(f23053,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f22662,f5854])).

fof(f5854,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5853,f5575])).

fof(f5575,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5574,f2849])).

fof(f2849,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f134,f120])).

fof(f5574,plain,(
    k1_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5526,f3816])).

fof(f5526,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f133,f134,f93])).

fof(f5853,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5852,f3013])).

fof(f5852,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5454,f2995])).

fof(f5454,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f134,f133,f93])).

fof(f22662,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f1213,f110])).

fof(f22889,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f22822,f22864])).

fof(f22822,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f1213,f122])).

fof(f22864,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f1213,f123])).

fof(f49784,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f49783,f2001])).

fof(f49783,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f49782,f2006])).

fof(f49782,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f46862,f3817])).

fof(f46862,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f199,f134,f133,f82])).

fof(f22872,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f1213,f123])).

fof(f50751,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50750,f49378])).

fof(f49378,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f48143,f49327])).

fof(f49327,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f49326,f49201])).

fof(f49201,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f49200,f32823])).

fof(f32823,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f32611,f32822])).

fof(f32822,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32419,f6167])).

fof(f6167,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f6166,f3302])).

fof(f6166,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) ),
    inference(forward_demodulation,[],[f6165,f6149])).

fof(f6149,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f6148,f3302])).

fof(f6148,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f6147,f4571])).

fof(f6147,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f5345,f3383])).

fof(f3383,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2757,f1947])).

fof(f2757,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f199,f120])).

fof(f5345,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f199,f132,f93])).

fof(f6165,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f5337,f2799])).

fof(f2799,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f203,f120])).

fof(f5337,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f203,f132,f93])).

fof(f32419,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f199,f1640,f110])).

fof(f32611,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f1640,f122])).

fof(f49200,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f49199,f47524])).

fof(f47524,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47523,f38688])).

fof(f47523,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f47522,f4097])).

fof(f4097,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f132,f123])).

fof(f47522,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f47521,f4456])).

fof(f4456,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f4121,f3796])).

fof(f3796,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(forward_demodulation,[],[f3773,f3784])).

fof(f3784,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(backward_demodulation,[],[f2990,f3781])).

fof(f3781,plain,(
    sK9(sK0) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f2989,f3780])).

fof(f3780,plain,(
    sK9(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(backward_demodulation,[],[f982,f3775])).

fof(f982,plain,(
    sK9(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f134,f114])).

fof(f2989,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2847,f2004])).

fof(f2004,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f134,f119])).

fof(f2847,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f134,f120])).

fof(f2990,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f1552,f2989])).

fof(f1552,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f203,f110])).

fof(f3773,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f134,f122])).

fof(f4121,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f134,f123])).

fof(f47521,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47520,f32850])).

fof(f32850,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f32639,f32845])).

fof(f32845,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f32668,f32844])).

fof(f32844,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f32409,f5724])).

fof(f5724,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(backward_demodulation,[],[f5659,f5717])).

fof(f5717,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5716,f2848])).

fof(f5716,plain,(
    k1_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5715,f3780])).

fof(f5715,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5714,f5659])).

fof(f5714,plain,(
    k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5500,f2803])).

fof(f5500,plain,(
    k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f132,f203,f134,f93])).

fof(f5659,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5658,f3508])).

fof(f3508,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2682,f1942])).

fof(f1942,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f203,f119])).

fof(f2682,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f189,f120])).

fof(f5658,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5657,f2848])).

fof(f5657,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5516,f3302])).

fof(f5516,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f132,f134,f93])).

fof(f32409,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f1640,f110])).

fof(f32668,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32591,f32639])).

fof(f32591,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f1640,f122])).

fof(f32639,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f1640,f123])).

fof(f47520,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47519,f1968])).

fof(f47519,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47119,f3781])).

fof(f47119,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f203,f132,f134,f82])).

fof(f49199,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f49198,f8141])).

fof(f49198,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f49197,f32850])).

fof(f49197,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f49196,f32694])).

fof(f32694,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32547,f6167])).

fof(f32547,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f1640,f120])).

fof(f49196,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f46930,f32703])).

fof(f32703,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f32537,f5724])).

fof(f32537,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f1640,f120])).

fof(f46930,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f199,f1640,f134,f82])).

fof(f49326,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f49325,f27587])).

fof(f27587,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f27387,f27586])).

fof(f27586,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f27207,f5996])).

fof(f5996,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f5995,f3149])).

fof(f5995,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) ),
    inference(forward_demodulation,[],[f5994,f5950])).

fof(f5950,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5949,f3149])).

fof(f5949,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5948,f3816])).

fof(f5948,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5425,f3385])).

fof(f5425,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f199,f133,f93])).

fof(f5994,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f5409,f2784])).

fof(f5409,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f202,f133,f93])).

fof(f27207,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f199,f1490,f110])).

fof(f27387,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f1490,f122])).

fof(f49325,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f49324,f47338])).

fof(f47338,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47337,f1949])).

fof(f47337,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47336,f38687])).

fof(f47336,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f47335,f8180])).

fof(f47335,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f47334,f4460])).

fof(f4460,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f4120,f3798])).

fof(f3798,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(forward_demodulation,[],[f3772,f3792])).

fof(f3792,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(backward_demodulation,[],[f2992,f3789])).

fof(f3789,plain,(
    sK9(sK0) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f2991,f3788])).

fof(f2991,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2846,f2003])).

fof(f2003,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f134,f119])).

fof(f2846,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f134,f120])).

fof(f2992,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f1406,f2991])).

fof(f1406,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f202,f110])).

fof(f3772,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f134,f122])).

fof(f4120,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f134,f123])).

fof(f47334,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47333,f27613])).

fof(f27613,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f27414,f27608])).

fof(f27608,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f27440,f27607])).

fof(f27607,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f27198,f5756])).

fof(f5756,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(backward_demodulation,[],[f5604,f5749])).

fof(f5749,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5748,f2849])).

fof(f5748,plain,(
    k1_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5747,f3788])).

fof(f5747,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5746,f5604])).

fof(f5746,plain,(
    k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5492,f2789])).

fof(f2789,plain,(
    k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f202,f120])).

fof(f5492,plain,(
    k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f133,f202,f134,f93])).

fof(f5604,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5603,f3478])).

fof(f3478,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2696,f1925])).

fof(f1925,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f202,f119])).

fof(f2696,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f190,f120])).

fof(f5603,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5602,f2849])).

fof(f5602,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5524,f3149])).

fof(f5524,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f133,f134,f93])).

fof(f27198,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f1490,f110])).

fof(f27440,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f27369,f27414])).

fof(f27369,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f1490,f122])).

fof(f27414,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f1490,f123])).

fof(f47333,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47332,f1985])).

fof(f47332,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47135,f3789])).

fof(f47135,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f202,f133,f134,f82])).

fof(f49324,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f49323,f8141])).

fof(f49323,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f49322,f27613])).

fof(f49322,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f49321,f27466])).

fof(f27466,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f27327,f5996])).

fof(f27327,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f1490,f120])).

fof(f49321,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f46913,f27474])).

fof(f27474,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f27318,f5756])).

fof(f27318,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f1490,f120])).

fof(f46913,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f199,f1490,f134,f82])).

fof(f48143,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48142,f38703])).

fof(f38703,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f38458,f38689])).

fof(f38689,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f38475,f8144])).

fof(f8144,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3899,f8141])).

fof(f3899,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f1183,f3704])).

fof(f3704,plain,(
    k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f199,f122])).

fof(f1183,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f199,f114])).

fof(f38475,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f1676,f120])).

fof(f38458,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f1676,f119])).

fof(f48142,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48141,f27592])).

fof(f27592,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f27417,f27587])).

fof(f27417,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f1490,f123])).

fof(f48141,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f48140,f8145])).

fof(f48140,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f48139,f47339])).

fof(f47339,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f27423,f47338])).

fof(f27423,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f1490,f123])).

fof(f48139,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48138,f27480])).

fof(f27480,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f27312,f6300])).

fof(f6300,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f6299,f3149])).

fof(f6299,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f6298,f3819])).

fof(f3819,plain,(
    sK8(sK0) = k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f2759,f3817])).

fof(f2759,plain,(
    k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f199,f120])).

fof(f6298,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f5281,f3149])).

fof(f5281,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f133,f199,f93])).

fof(f27312,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f1490,f120])).

fof(f48138,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48137,f2001])).

fof(f48137,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f47057,f27460])).

fof(f27460,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f27333,f5987])).

fof(f5987,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f5986,f3013])).

fof(f5986,plain,(
    k1_lattices(sK0,sK9(sK0),sK8(sK0)) = k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f5985,f3149])).

fof(f5985,plain,(
    k1_lattices(sK0,sK9(sK0),sK8(sK0)) = k1_lattices(sK0,sK9(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) ),
    inference(forward_demodulation,[],[f5412,f3791])).

fof(f3791,plain,(
    sK9(sK0) = k1_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f2790,f3789])).

fof(f2790,plain,(
    k1_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f202,f120])).

fof(f5412,plain,(
    k1_lattices(sK0,sK9(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f134,f202,f133,f93])).

fof(f27333,plain,(
    k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f1490,f120])).

fof(f47057,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f1490,f199,f134,f82])).

fof(f50750,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f50749,f49329])).

fof(f49329,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f27410,f49327])).

fof(f27410,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f1213,f1490,f123])).

fof(f50749,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f50748,f22929])).

fof(f22929,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f22767,f6674])).

fof(f6674,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f6673,f2995])).

fof(f6673,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f6672,f3791])).

fof(f6672,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5130,f2995])).

fof(f5130,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f134,f202,f93])).

fof(f22767,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f1213,f120])).

fof(f50748,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f50747,f1985])).

fof(f50747,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f46784,f22909])).

fof(f22909,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f22788,f5694])).

fof(f5694,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f5693,f2849])).

fof(f5693,plain,(
    k1_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f5692,f2995])).

fof(f5692,plain,(
    k1_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5510,f3819])).

fof(f5510,plain,(
    k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f133,f199,f134,f93])).

fof(f22788,plain,(
    k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f1213,f120])).

fof(f46784,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) ),
    inference(unit_resulting_resolution,[],[f1213,f202,f133,f82])).

fof(f50737,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50736,f38701])).

fof(f50736,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50735,f32836])).

fof(f32836,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f32641,f32831])).

fof(f32831,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f32609,f32830])).

fof(f32830,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32417,f6192])).

fof(f6192,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f6191,f3302])).

fof(f6191,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f6190,f4394])).

fof(f6190,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f6189,f6171])).

fof(f6171,plain,(
    k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f6170,f3302])).

fof(f6170,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f5335,f2801])).

fof(f5335,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f203,f132,f93])).

fof(f6189,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f5327,f3347])).

fof(f5327,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f202,f132,f93])).

fof(f32417,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f202,f1640,f110])).

fof(f32609,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f1640,f122])).

fof(f32641,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f1640,f123])).

fof(f50735,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50734,f8180])).

fof(f50734,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50733,f50137])).

fof(f50137,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f32648,f50136])).

fof(f50136,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f50135,f38689])).

fof(f50135,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f50134,f4097])).

fof(f50134,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f50133,f4629])).

fof(f4629,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f4109,f4290])).

fof(f4290,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(backward_demodulation,[],[f3761,f4287])).

fof(f4287,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(backward_demodulation,[],[f3148,f4284])).

fof(f4284,plain,(
    sK8(sK0) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3147,f4235])).

fof(f3147,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2832,f1986])).

fof(f1986,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f133,f119])).

fof(f2832,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f133,f120])).

fof(f3148,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f1551,f3147])).

fof(f1551,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f203,f110])).

fof(f3761,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f133,f122])).

fof(f4109,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f133,f123])).

fof(f50133,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50132,f32863])).

fof(f32863,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f32638,f32858])).

fof(f50132,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f50131,f1968])).

fof(f50131,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f46830,f4284])).

fof(f46830,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f203,f132,f133,f82])).

fof(f32648,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f1640,f123])).

fof(f50733,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f50732,f32711])).

fof(f32711,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f32529,f6724])).

fof(f6724,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f6723,f3302])).

fof(f6723,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f6722,f4447])).

fof(f4447,plain,(
    sK7(sK0) = k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f2788,f4445])).

fof(f2788,plain,(
    k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f202,f120])).

fof(f6722,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5111,f3302])).

fof(f5111,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f132,f202,f93])).

fof(f32529,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f1640,f120])).

fof(f50732,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f50731,f1985])).

fof(f50731,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f46786,f32689])).

fof(f32689,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32552,f6161])).

fof(f6161,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f6160,f3175])).

fof(f6160,plain,(
    k1_lattices(sK0,sK8(sK0),sK7(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f6159,f3302])).

fof(f6159,plain,(
    k1_lattices(sK0,sK8(sK0),sK7(sK0)) = k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) ),
    inference(forward_demodulation,[],[f5339,f4286])).

fof(f4286,plain,(
    sK8(sK0) = k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f2804,f4284])).

fof(f2804,plain,(
    k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f203,f120])).

fof(f5339,plain,(
    k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f133,f203,f132,f93])).

fof(f32552,plain,(
    k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f1640,f120])).

fof(f46786,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f1640,f202,f133,f82])).

fof(f53824,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f53823,f51347])).

fof(f51347,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51346,f18967])).

fof(f18967,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f18966,f10809])).

fof(f10809,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f10808,f5755])).

fof(f5755,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3479,f5749])).

fof(f3479,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f1397,f3478])).

fof(f1397,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f190,f202,f110])).

fof(f10808,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f10807,f3654])).

fof(f3654,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f190,f122])).

fof(f10807,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f10406,f8542])).

fof(f8542,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f8541,f5927])).

fof(f5927,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3719,f5923])).

fof(f5923,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f4710,f5921])).

fof(f5921,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3574,f5916])).

fof(f5916,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3573,f5915])).

fof(f3573,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2651,f1921])).

fof(f1921,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f202,f119])).

fof(f2651,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f186,f120])).

fof(f3574,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f1393,f3573])).

fof(f1393,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f186,f202,f110])).

fof(f4710,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3664,f4067])).

fof(f4067,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f202,f123])).

fof(f3664,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f186,f122])).

fof(f3719,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f202,f122])).

fof(f8541,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f8540,f4389])).

fof(f8540,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,sK9(sK0),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f7944,f4475])).

fof(f7944,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,sK9(sK0),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f186,f134,f132,f98])).

fof(f10406,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f310,f98])).

fof(f18966,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f18923,f18949])).

fof(f18949,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f310,f642,f123])).

fof(f18923,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f310,f642,f122])).

fof(f51346,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51345,f10602])).

fof(f10602,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(backward_demodulation,[],[f10595,f10601])).

fof(f10601,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f10575,f8283])).

fof(f8283,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f8282,f3775])).

fof(f8282,plain,(
    k2_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f8281,f4475])).

fof(f8281,plain,(
    k2_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) ),
    inference(forward_demodulation,[],[f8057,f3176])).

fof(f3176,plain,(
    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f417,f3175])).

fof(f417,plain,(
    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k1_lattices(sK0,sK8(sK0),sK7(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f132,f110])).

fof(f8057,plain,(
    k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f133,f186,f134,f98])).

fof(f10575,plain,(
    k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f310,f122])).

fof(f10595,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f310,f123])).

fof(f51345,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51344,f18959])).

fof(f18959,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f18927,f8673])).

fof(f8673,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8672,f4568])).

fof(f8672,plain,(
    k2_lattices(sK0,sK8(sK0),sK7(sK0)) = k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8671,f4677])).

fof(f8671,plain,(
    k2_lattices(sK0,sK8(sK0),sK7(sK0)) = k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) ),
    inference(forward_demodulation,[],[f7886,f2983])).

fof(f2983,plain,(
    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f433,f2849])).

fof(f433,plain,(
    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f134,f110])).

fof(f7886,plain,(
    k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f133,f190,f132,f98])).

fof(f18927,plain,(
    k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f642,f122])).

fof(f51344,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f51343,f51111])).

fof(f51111,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f51110,f1929])).

fof(f51110,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f51109,f18968])).

fof(f18968,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18949,f18967])).

fof(f51109,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f51108,f18960])).

fof(f18960,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(backward_demodulation,[],[f18953,f18959])).

fof(f18953,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f642,f123])).

fof(f51108,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f51107,f10601])).

fof(f51107,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f51106,f18845])).

fof(f18845,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f310,f642,f119])).

fof(f51106,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f51105,f18849])).

fof(f18849,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f642,f119])).

fof(f51105,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f46739,f50295])).

fof(f50295,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f49909,f50294])).

fof(f50294,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50293,f18849])).

fof(f50293,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f50292,f19060])).

fof(f19060,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f18844,f19057])).

fof(f19057,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18870,f19056])).

fof(f19056,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f18797,f8673])).

fof(f18797,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f642,f114])).

fof(f18870,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f642,f120])).

fof(f18844,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f642,f119])).

fof(f50292,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f50291,f4090])).

fof(f50291,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f50290,f3951])).

fof(f3951,plain,(
    sK8(sK0) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f3655,f2983])).

fof(f3655,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f190,f122])).

fof(f50290,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50289,f15876])).

fof(f15876,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f15855,f15875])).

fof(f15875,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f15831,f5571])).

fof(f5571,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f3010,f5567])).

fof(f5567,plain,(
    k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3009,f5566])).

fof(f5566,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5565,f2698])).

fof(f2698,plain,(
    k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f190,f120])).

fof(f5565,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5564,f2849])).

fof(f5564,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5527,f2833])).

fof(f5527,plain,(
    k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f132,f133,f134,f93])).

fof(f3009,plain,(
    k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) ),
    inference(forward_demodulation,[],[f2837,f1993])).

fof(f1993,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f134,f119])).

fof(f2837,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f134,f120])).

fof(f3010,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f430,f3009])).

fof(f430,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f186,f134,f110])).

fof(f15831,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f620,f122])).

fof(f620,plain,(
    m1_subset_1(k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f190,f118])).

fof(f15855,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f620,f123])).

fof(f50289,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f50288,f1961])).

fof(f1961,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f132,f119])).

fof(f50288,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f46823,f3470])).

fof(f3470,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2699,f2984])).

fof(f2984,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f917,f2983])).

fof(f917,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f190,f114])).

fof(f2699,plain,(
    k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f190,f120])).

fof(f46823,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f190,f132,f133,f82])).

fof(f49909,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f4006,f49908])).

fof(f49908,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f49907,f10515])).

fof(f10515,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f310,f119])).

fof(f49907,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f49906,f10677])).

fof(f10677,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f10511,f10674])).

fof(f10674,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f10531,f10673])).

fof(f10673,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f10475,f8283])).

fof(f10475,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f310,f114])).

fof(f10531,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f310,f120])).

fof(f10511,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f310,f119])).

fof(f49906,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f49905,f4115])).

fof(f49905,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f49904,f4123])).

fof(f49904,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f49903,f3936])).

fof(f3936,plain,(
    sK8(sK0) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f3667,f3176])).

fof(f3667,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f186,f122])).

fof(f49903,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f49902,f15878])).

fof(f15878,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f15854,f15877])).

fof(f15877,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f15830,f3317])).

fof(f3317,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f587,f3316])).

fof(f3316,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2810,f1961])).

fof(f2810,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f132,f120])).

fof(f587,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f190,f110])).

fof(f15830,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f620,f122])).

fof(f15854,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f620,f123])).

fof(f49902,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f49901,f5569])).

fof(f5569,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f1993,f5567])).

fof(f49901,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f49900,f2006])).

fof(f49900,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f46855,f3561])).

fof(f3561,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f2654,f3177])).

fof(f3177,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f865,f3176])).

fof(f865,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f186,f114])).

fof(f2654,plain,(
    k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f186,f120])).

fof(f46855,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f186,f134,f133,f82])).

fof(f46739,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) ),
    inference(unit_resulting_resolution,[],[f310,f642,f133,f82])).

fof(f51343,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f46707,f50297])).

fof(f50297,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f10515,f50295])).

fof(f46707,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f642,f310,f133,f82])).

fof(f53823,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f53822,f1949])).

fof(f53822,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f53821,f10601])).

fof(f53821,plain,(
    k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f53820,f10604])).

fof(f10604,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(backward_demodulation,[],[f10594,f10603])).

fof(f10603,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f10574,f8286])).

fof(f10574,plain,(
    k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f310,f122])).

fof(f10594,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f310,f123])).

fof(f53820,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f53819,f52841])).

fof(f52841,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f52840,f48480])).

fof(f48480,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48479,f18964])).

fof(f18964,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f18963,f13216])).

fof(f13216,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f13215,f5577])).

fof(f5577,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3483,f5576])).

fof(f5576,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3482,f5575])).

fof(f3482,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f2694,f1889])).

fof(f1889,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f199,f119])).

fof(f2694,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f190,f120])).

fof(f3483,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f1131,f3482])).

fof(f1131,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f190,f199,f110])).

fof(f13215,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f13214,f3654])).

fof(f13214,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f12773,f8570])).

fof(f8570,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f8569,f5655])).

fof(f5655,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3693,f5651])).

fof(f5651,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f4743,f5646])).

fof(f5646,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3515,f5645])).

fof(f5645,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3514,f5644])).

fof(f3514,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f2679,f1888])).

fof(f1888,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f199,f119])).

fof(f2679,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f189,f120])).

fof(f3515,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f1130,f3514])).

fof(f1130,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f189,f199,f110])).

fof(f4743,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3638,f4041])).

fof(f4041,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f199,f123])).

fof(f3638,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f189,f122])).

fof(f3693,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f199,f122])).

fof(f8569,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f8568,f4568])).

fof(f8568,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,sK8(sK0),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f7933,f4654])).

fof(f4654,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(backward_demodulation,[],[f3753,f4101])).

fof(f4101,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f133,f123])).

fof(f3753,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f133,f122])).

fof(f7933,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,sK8(sK0),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f189,f133,f132,f98])).

fof(f12773,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f569,f98])).

fof(f569,plain,(
    m1_subset_1(k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f189,f121])).

fof(f18963,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f18924,f18950])).

fof(f18950,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f569,f642,f123])).

fof(f18924,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f569,f642,f122])).

fof(f48479,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48478,f12986])).

fof(f12986,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(backward_demodulation,[],[f12982,f12985])).

fof(f12985,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f12960,f8499])).

fof(f8499,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8498,f4232])).

fof(f4232,plain,(
    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK9(sK0),sK8(sK0)) ),
    inference(backward_demodulation,[],[f3764,f4123])).

fof(f8498,plain,(
    k2_lattices(sK0,sK9(sK0),sK8(sK0)) = k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8497,f4654])).

fof(f8497,plain,(
    k2_lattices(sK0,sK9(sK0),sK8(sK0)) = k2_lattices(sK0,sK9(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) ),
    inference(forward_demodulation,[],[f7959,f3172])).

fof(f3172,plain,(
    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f418,f3171])).

fof(f418,plain,(
    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k1_lattices(sK0,sK9(sK0),sK7(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f132,f110])).

fof(f7959,plain,(
    k2_lattices(sK0,sK9(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f134,f189,f133,f98])).

fof(f12960,plain,(
    k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f569,f122])).

fof(f12982,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f569,f123])).

fof(f48478,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48477,f18957])).

fof(f48477,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48476,f48365])).

fof(f48365,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f48364,f18965])).

fof(f18965,plain,(
    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18950,f18964])).

fof(f48364,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48363,f18958])).

fof(f18958,plain,(
    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(backward_demodulation,[],[f18954,f18957])).

fof(f18954,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f642,f123])).

fof(f48363,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48362,f12985])).

fof(f48362,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f48361,f18846])).

fof(f18846,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f569,f642,f119])).

fof(f48361,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f48360,f18850])).

fof(f18850,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f642,f119])).

fof(f48360,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f47029,f47625])).

fof(f47625,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f47431,f47624])).

fof(f47624,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47623,f18850])).

fof(f47623,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47622,f19055])).

fof(f19055,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f18842,f19052])).

fof(f19052,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18868,f19051])).

fof(f19051,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f18798,f8670])).

fof(f18798,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f642,f114])).

fof(f18868,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f642,f120])).

fof(f18842,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f642,f119])).

fof(f47622,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47621,f4090])).

fof(f47621,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47620,f3949])).

fof(f3949,plain,(
    sK9(sK0) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f3656,f3014])).

fof(f3656,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f190,f122])).

fof(f47620,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47619,f15880])).

fof(f15880,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f15853,f15879])).

fof(f15879,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f15829,f5631])).

fof(f5631,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f3164,f5626])).

fof(f5626,plain,(
    k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5625,f5566])).

fof(f5625,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5624,f2684])).

fof(f2684,plain,(
    k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f189,f120])).

fof(f5624,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5623,f2848])).

fof(f5623,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f5519,f3175])).

fof(f5519,plain,(
    k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK8(sK0),sK7(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f133,f132,f134,f93])).

fof(f3164,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f519,f3163])).

fof(f3163,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2824,f1978])).

fof(f1978,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f133,f119])).

fof(f2824,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f133,f120])).

fof(f519,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f189,f110])).

fof(f15829,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f620,f122])).

fof(f15853,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f620,f123])).

fof(f47619,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f47618,f1961])).

fof(f47618,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f47112,f3465])).

fof(f3465,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2700,f3015])).

fof(f3015,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f918,f3014])).

fof(f918,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f190,f114])).

fof(f2700,plain,(
    k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f190,f120])).

fof(f47112,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f190,f132,f134,f82])).

fof(f47431,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f3993,f47430])).

fof(f47430,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47429,f12894])).

fof(f12894,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f569,f119])).

fof(f47429,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47428,f13068])).

fof(f13068,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f12888,f13065])).

fof(f13065,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f12910,f13064])).

fof(f13064,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f12850,f8499])).

fof(f12850,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f569,f114])).

fof(f12910,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f569,f120])).

fof(f12888,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f569,f119])).

fof(f47428,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47427,f4101])).

fof(f47427,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f47426,f3963])).

fof(f3963,plain,(
    sK9(sK0) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f3644,f3172])).

fof(f3644,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f189,f122])).

fof(f47426,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47425,f15878])).

fof(f47425,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f47424,f5628])).

fof(f5628,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f1978,f5626])).

fof(f47424,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f47128,f3497])).

fof(f3497,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2685,f3173])).

fof(f3173,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f905,f3172])).

fof(f905,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f189,f114])).

fof(f2685,plain,(
    k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f189,f120])).

fof(f47128,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f189,f133,f134,f82])).

fof(f3993,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f190,f123])).

fof(f47029,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f569,f642,f134,f82])).

fof(f48476,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f47013,f47627])).

fof(f47627,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f12894,f47625])).

fof(f47013,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f642,f569,f134,f82])).

fof(f52840,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f52839,f1947])).

fof(f52839,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f52838,f10602])).

fof(f52838,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f52837,f4110])).

fof(f52837,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f52836,f10603])).

fof(f52836,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f52835,f51825])).

fof(f51825,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f51133,f51824])).

fof(f51824,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f51823,f51507])).

fof(f51507,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51506,f50355])).

fof(f50355,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f49908,f50295])).

fof(f51506,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51505,f18849])).

fof(f51505,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51504,f4649])).

fof(f4649,plain,(
    sK8(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(forward_demodulation,[],[f4102,f3951])).

fof(f4102,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f133,f123])).

fof(f51504,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51503,f4110])).

fof(f51503,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) ),
    inference(forward_demodulation,[],[f51502,f15878])).

fof(f51502,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51501,f3473])).

fof(f3473,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) ),
    inference(backward_demodulation,[],[f1979,f3470])).

fof(f1979,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f133,f119])).

fof(f51501,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f46695,f1987])).

fof(f46695,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK7(sK0))) ),
    inference(unit_resulting_resolution,[],[f132,f190,f133,f82])).

fof(f51823,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51822,f18849])).

fof(f51822,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51821,f18978])).

fof(f51821,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51820,f4645])).

fof(f4645,plain,(
    sK8(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(forward_demodulation,[],[f4103,f3936])).

fof(f4103,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f133,f123])).

fof(f51820,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51819,f18959])).

fof(f51819,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f51818,f325])).

fof(f325,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f130,f131,f81,f186,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X1) = X1
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattices)).

fof(f51818,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f51817,f19091])).

fof(f19091,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f18840,f19089])).

fof(f19089,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f19031,f19088])).

fof(f19088,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f18775,f9299])).

fof(f9299,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f9298,f4677])).

fof(f9298,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f9297,f3144])).

fof(f9297,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f7601,f4677])).

fof(f7601,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f186,f98])).

fof(f18775,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f186,f642,f114])).

fof(f19031,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18853,f18840])).

fof(f18853,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f642,f120])).

fof(f18840,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f642,f119])).

fof(f51817,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f46656,f3564])).

fof(f3564,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(backward_demodulation,[],[f1975,f3561])).

fof(f1975,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f133,f119])).

fof(f46656,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f642,f186,f133,f82])).

fof(f51133,plain,(
    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51132,f18849])).

fof(f51132,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51131,f19060])).

fof(f51131,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51130,f18977])).

fof(f51130,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f51129,f18960])).

fof(f51129,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f51128,f3936])).

fof(f51128,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51127,f19089])).

fof(f51127,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f51126,f18849])).

fof(f51126,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f46736,f3561])).

fof(f46736,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f186,f642,f133,f82])).

fof(f52835,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f52834,f50297])).

fof(f52834,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f52833,f1987])).

fof(f52833,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK7(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f46552,f50402])).

fof(f50402,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50401,f4618])).

fof(f50401,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50400,f4679])).

fof(f4679,plain,(
    sK7(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(forward_demodulation,[],[f4089,f3966])).

fof(f4089,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f132,f123])).

fof(f50400,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50399,f47735])).

fof(f47735,plain,(
    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47734,f4445])).

fof(f47734,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f47733,f4672])).

fof(f47733,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47732,f3569])).

fof(f3569,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f1957,f3566])).

fof(f3566,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f2653,f3145])).

fof(f3145,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f864,f3144])).

fof(f864,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f186,f114])).

fof(f2653,plain,(
    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f186,f120])).

fof(f1957,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f132,f119])).

fof(f47732,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47110,f5567])).

fof(f47110,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f186,f132,f134,f82])).

fof(f50399,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50398,f4005])).

fof(f4005,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f186,f123])).

fof(f50398,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f50397,f3506])).

fof(f3506,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f1960,f3503])).

fof(f3503,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f2683,f2987])).

fof(f2987,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f903,f2986])).

fof(f903,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f189,f114])).

fof(f2683,plain,(
    k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f189,f120])).

fof(f1960,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f132,f119])).

fof(f50397,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f46822,f5626])).

fof(f46822,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f189,f132,f133,f82])).

fof(f46552,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK7(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) ),
    inference(unit_resulting_resolution,[],[f310,f133,f132,f82])).

fof(f53819,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f53818,f50295])).

fof(f53818,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f46424,f50404])).

fof(f50404,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f10514,f50402])).

fof(f10514,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f310,f119])).

fof(f46424,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f133,f310,f132,f82])).

fof(f51352,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f49766,f51347])).

fof(f49766,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f49765,f4123])).

fof(f49765,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f49764,f4110])).

fof(f49764,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f49763,f47624])).

fof(f49763,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f49762,f2006])).

fof(f49762,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f46865,f1987])).

fof(f46865,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK7(sK0))) ),
    inference(unit_resulting_resolution,[],[f132,f134,f133,f82])).

fof(f64586,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f64585,f49668])).

fof(f49668,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f49667,f48773])).

fof(f48773,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48772,f47681])).

fof(f47681,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f47430,f47625])).

fof(f48772,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48771,f18850])).

fof(f48771,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48770,f4477])).

fof(f4477,plain,(
    sK9(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(forward_demodulation,[],[f4114,f3949])).

fof(f4114,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f134,f123])).

fof(f48770,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48769,f4122])).

fof(f48769,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),sK7(sK0))) ),
    inference(forward_demodulation,[],[f48768,f15878])).

fof(f48768,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f48767,f3468])).

fof(f3468,plain,(
    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(backward_demodulation,[],[f1997,f3465])).

fof(f1997,plain,(
    k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f134,f119])).

fof(f48767,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f46984,f2005])).

fof(f46984,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k3_lattices(sK0,sK9(sK0),sK7(sK0))) ),
    inference(unit_resulting_resolution,[],[f132,f190,f134,f82])).

fof(f49667,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f49666,f18850])).

fof(f49666,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f49665,f18976])).

fof(f18976,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18945,f18975])).

fof(f18975,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f18919,f16126])).

fof(f16126,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f16125,f3654])).

fof(f16125,plain,(
    k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f15636,f15883])).

fof(f15883,plain,(
    sK7(sK0) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f15826,f15872])).

fof(f15872,plain,(
    sK7(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(backward_demodulation,[],[f15862,f15871])).

fof(f15871,plain,(
    sK7(sK0) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f15838,f3475])).

fof(f3475,plain,(
    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f598,f2698])).

fof(f598,plain,(
    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f190,f110])).

fof(f15838,plain,(
    k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f620,f122])).

fof(f15862,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f620,f123])).

fof(f15826,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f620,f122])).

fof(f15636,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f620,f98])).

fof(f18919,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f620,f642,f122])).

fof(f18945,plain,(
    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f620,f642,f123])).

fof(f49665,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f49664,f15868])).

fof(f15868,plain,(
    sK9(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(backward_demodulation,[],[f15864,f15867])).

fof(f15867,plain,(
    sK9(sK0) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f15840,f5572])).

fof(f5572,plain,(
    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f3560,f5567])).

fof(f3560,plain,(
    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f402,f2655])).

fof(f2655,plain,(
    k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f186,f120])).

fof(f402,plain,(
    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f186,f110])).

fof(f15840,plain,(
    k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f620,f122])).

fof(f15864,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f620,f123])).

fof(f49664,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f49663,f18957])).

fof(f49663,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f49662,f16040])).

fof(f16040,plain,(
    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f15832,f16039])).

fof(f16039,plain,(
    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f15684,f5573])).

fof(f5573,plain,(
    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(backward_demodulation,[],[f5556,f5567])).

fof(f5556,plain,(
    k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5555,f3009])).

fof(f5555,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5554,f137])).

fof(f137,plain,(
    sK9(sK0) = k1_lattices(sK0,sK9(sK0),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f130,f131,f81,f134,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_lattices(X0,X1,X1) = X1
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

fof(f5554,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5532,f3009])).

fof(f5532,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f186,f134,f134,f93])).

fof(f15684,plain,(
    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f620,f110])).

fof(f15832,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f620,f620,f122])).

fof(f49662,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f49661,f19086])).

fof(f19086,plain,(
    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18841,f19084])).

fof(f19084,plain,(
    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f19030,f19083])).

fof(f19083,plain,(
    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f18776,f16590])).

fof(f16590,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f16589,f4677])).

fof(f16589,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f16588,f3475])).

fof(f16588,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f15348,f4677])).

fof(f15348,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f620,f98])).

fof(f18776,plain,(
    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f620,f642,f114])).

fof(f19030,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18854,f18841])).

fof(f18854,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f620,f642,f120])).

fof(f18841,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f620,f642,f119])).

fof(f49661,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f46877,f15918])).

fof(f15918,plain,(
    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f15780,f5573])).

fof(f15780,plain,(
    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f620,f120])).

fof(f46877,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f642,f620,f134,f82])).

fof(f64585,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f64584,f5569])).

fof(f64584,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f45121,f19091])).

fof(f45121,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f186,f134,f642,f82])).

fof(f51385,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18845,f51384])).

fof(f51384,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f48524,f51383])).

fof(f51383,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51382,f10677])).

fof(f51382,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51381,f10615])).

fof(f10615,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f10567,f8330])).

fof(f8330,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f8301,f8329])).

fof(f8329,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f8328,f4475])).

fof(f8328,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f8327,f4483])).

fof(f4483,plain,(
    sK9(sK0) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(backward_demodulation,[],[f3765,f4481])).

fof(f4481,plain,(
    sK9(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(forward_demodulation,[],[f4113,f3963])).

fof(f4113,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f134,f123])).

fof(f3765,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f134,f122])).

fof(f8327,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f8034,f3635])).

fof(f3635,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f189,f122])).

fof(f8034,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f186,f189,f134,f98])).

fof(f8301,plain,(
    k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f8300,f4475])).

fof(f8300,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f8050,f4782])).

fof(f4782,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(backward_demodulation,[],[f3657,f4005])).

fof(f3657,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f186,f122])).

fof(f8050,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f189,f186,f134,f98])).

fof(f10567,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f310,f122])).

fof(f51381,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51380,f10602])).

fof(f51380,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51379,f51125])).

fof(f51125,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51124,f19060])).

fof(f51124,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51123,f18981])).

fof(f18981,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f18916,f8707])).

fof(f8707,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8706,f4677])).

fof(f8706,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8705,f4681])).

fof(f4681,plain,(
    sK7(sK0) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(backward_demodulation,[],[f3741,f4679])).

fof(f3741,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f132,f122])).

fof(f8705,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8704,f8692])).

fof(f8692,plain,(
    k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8691,f4677])).

fof(f8691,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f7879,f3645])).

fof(f3645,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f190,f122])).

fof(f7879,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f189,f190,f132,f98])).

fof(f8704,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f7871,f4790])).

fof(f4790,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(backward_demodulation,[],[f3634,f3993])).

fof(f3634,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f189,f122])).

fof(f7871,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f189,f132,f98])).

fof(f18916,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f642,f122])).

fof(f51123,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51122,f18960])).

fof(f51122,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51121,f19095])).

fof(f19095,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f19034,f19094])).

fof(f19094,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f18773,f9701])).

fof(f9701,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f9700,f4677])).

fof(f9700,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f9699,f2986])).

fof(f9699,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f7439,f4677])).

fof(f7439,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f189,f98])).

fof(f18773,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f189,f642,f114])).

fof(f19034,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18851,f18838])).

fof(f18838,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f642,f119])).

fof(f18851,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f642,f120])).

fof(f51121,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51120,f18849])).

fof(f51120,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f46737,f5626])).

fof(f46737,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f189,f642,f133,f82])).

fof(f51379,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51378,f10704])).

fof(f10704,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f10656,f10703])).

fof(f10703,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f10457,f9651])).

fof(f9651,plain,(
    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f9650,f4475])).

fof(f9650,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f9649,f3172])).

fof(f9649,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(forward_demodulation,[],[f7458,f4475])).

fof(f7458,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f186,f134,f189,f98])).

fof(f10457,plain,(
    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f189,f310,f114])).

fof(f10656,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f10517,f10507])).

fof(f10507,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f310,f119])).

fof(f10517,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f310,f120])).

fof(f51378,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f51377,f50297])).

fof(f51377,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f46703,f5626])).

fof(f46703,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f189,f310,f133,f82])).

fof(f48524,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f12890,f48523])).

fof(f48523,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f48522,f13068])).

fof(f48522,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f48521,f13000])).

fof(f13000,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f12952,f8517])).

fof(f8517,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f8516,f4654])).

fof(f8516,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) ),
    inference(forward_demodulation,[],[f8515,f8480])).

fof(f8480,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f8479,f4654])).

fof(f8479,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f8478,f4647])).

fof(f4647,plain,(
    sK8(sK0) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(backward_demodulation,[],[f3755,f4645])).

fof(f3755,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f133,f122])).

fof(f8478,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f7969,f4782])).

fof(f7969,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f189,f186,f133,f98])).

fof(f8515,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f7953,f3635])).

fof(f7953,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f186,f189,f133,f98])).

fof(f12952,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f569,f122])).

fof(f48521,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f48520,f12986])).

fof(f48520,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f48519,f48395])).

fof(f48395,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f48394,f19055])).

fof(f48394,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f48393,f18977])).

fof(f48393,plain,(
    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f48392,f18958])).

fof(f48392,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f48391,f19089])).

fof(f48391,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f48390,f18850])).

fof(f48390,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47025,f5567])).

fof(f47025,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f186,f642,f134,f82])).

fof(f48519,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f48518,f13094])).

fof(f13094,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f13046,f13093])).

fof(f13093,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f12831,f9277])).

fof(f9277,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f9276,f4654])).

fof(f9276,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f9275,f3176])).

fof(f9275,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(forward_demodulation,[],[f7609,f4654])).

fof(f7609,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f189,f133,f186,f98])).

fof(f12831,plain,(
    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f130,f186,f569,f114])).

fof(f13046,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f12897,f12886])).

fof(f12886,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f569,f119])).

fof(f12897,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f569,f120])).

fof(f48518,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f48517,f47627])).

fof(f48517,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f47008,f5567])).

fof(f47008,plain,(
    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f186,f569,f134,f82])).

fof(f12890,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f310,f569,f119])).

fof(f19106,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f18768,f19025])).

fof(f19025,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18872,f18846])).

fof(f18872,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f569,f642,f120])).

fof(f18768,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f569,f642,f110])).

fof(f55433,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(backward_demodulation,[],[f55332,f55370])).

fof(f55332,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f50176,f55295])).

fof(f50176,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(backward_demodulation,[],[f33729,f50137])).

fof(f33729,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f33728,f32588])).

fof(f32588,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f1490,f1640,f122])).

fof(f33728,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f33727,f32968])).

fof(f32968,plain,(
    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32967,f32662])).

fof(f32662,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32600,f32648])).

fof(f32600,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f1640,f122])).

fof(f32967,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32966,f3345])).

fof(f3345,plain,(
    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f1422,f2789])).

fof(f1422,plain,(
    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f202,f110])).

fof(f32966,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32362,f32662])).

fof(f32362,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f1490,f133,f1640,f98])).

fof(f33727,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32058,f33279])).

fof(f33279,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f32655,f33277])).

fof(f33277,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f32597,f33276])).

fof(f33276,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f33275,f32662])).

fof(f33275,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(forward_demodulation,[],[f33274,f4654])).

fof(f33274,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) ),
    inference(forward_demodulation,[],[f32230,f32844])).

fof(f32230,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f133,f189,f1640,f98])).

fof(f32597,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f569,f1640,f122])).

fof(f32655,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f32613,f32645])).

fof(f32645,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f569,f1640,f123])).

fof(f32613,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f569,f1640,f122])).

fof(f32058,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k2_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f1490,f569,f1640,f98])).

fof(f5733,plain,(
    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5732,f2995])).

fof(f5732,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5731,f3780])).

fof(f5731,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(forward_demodulation,[],[f5499,f2799])).

fof(f5499,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f203,f134,f93])).

fof(f47629,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f13038,f47625])).

fof(f13038,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f12905,f12894])).

fof(f12905,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f569,f120])).

fof(f19115,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) ),
    inference(forward_demodulation,[],[f18759,f19021])).

fof(f19021,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f18863,f18850])).

fof(f18863,plain,(
    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f642,f120])).

fof(f18759,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))) ),
    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f642,f110])).

fof(f52601,plain,(
    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f50220,f52539])).

fof(f50220,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) ),
    inference(backward_demodulation,[],[f23395,f50199])).

fof(f23395,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f22878,f23393])).

fof(f23393,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(backward_demodulation,[],[f22828,f23392])).

fof(f23392,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f23391,f22885])).

fof(f22885,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(forward_demodulation,[],[f22829,f22871])).

fof(f22829,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f1213,f122])).

fof(f23391,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) ),
    inference(forward_demodulation,[],[f23390,f4677])).

fof(f23390,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) ),
    inference(forward_demodulation,[],[f22519,f23053])).

fof(f22519,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f124,f129,f132,f190,f1213,f98])).

fof(f22828,plain,(
    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f642,f1213,f122])).

fof(f22878,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) ),
    inference(forward_demodulation,[],[f22842,f22870])).

fof(f22870,plain,(
    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f642,f1213,f123])).

fof(f22842,plain,(
    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) ),
    inference(unit_resulting_resolution,[],[f79,f128,f124,f642,f1213,f122])).

fof(f4809,plain,(
    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) != k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) ),
    inference(global_subsumption,[],[f81,f79,f4808])).

fof(f4808,plain,
    ( k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) != k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f4807,f3654])).

fof(f4807,plain,
    ( k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) != k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f4806,f2784])).

fof(f4806,plain,
    ( k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) != k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f4805,f2849])).

fof(f4805,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) != k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0)))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f4804,f3762])).

fof(f4804,plain,
    ( k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0))) != k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f4799,f3774])).

fof(f4799,plain,
    ( k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0))) != k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,sK7(sK0),sK9(sK0)))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f109,f83])).

fof(f109,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0)))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (2449)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (2434)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (2433)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (2440)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.52  % (2430)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (2438)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (2429)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.52  % (2441)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (2450)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (2431)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.53  % (2435)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.53  % (2451)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.53  % (2448)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.53  % (2442)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.53  % (2432)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.54  % (2432)Refutation not found, incomplete strategy% (2432)------------------------------
% 0.21/0.54  % (2432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2432)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2432)Memory used [KB]: 10618
% 0.21/0.54  % (2432)Time elapsed: 0.118 s
% 0.21/0.54  % (2432)------------------------------
% 0.21/0.54  % (2432)------------------------------
% 1.34/0.54  % (2436)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (2447)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.34/0.54  % (2443)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.34/0.54  % (2439)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.34/0.55  % (2444)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.34/0.56  % (2446)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.34/0.56  % (2445)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.64/0.57  % (2452)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.64/0.57  % (2439)Refutation not found, incomplete strategy% (2439)------------------------------
% 1.64/0.57  % (2439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (2439)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (2439)Memory used [KB]: 11129
% 1.64/0.57  % (2439)Time elapsed: 0.141 s
% 1.64/0.57  % (2439)------------------------------
% 1.64/0.57  % (2439)------------------------------
% 1.64/0.57  % (2452)Refutation not found, incomplete strategy% (2452)------------------------------
% 1.64/0.57  % (2452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (2452)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (2452)Memory used [KB]: 10746
% 1.64/0.57  % (2452)Time elapsed: 0.154 s
% 1.64/0.57  % (2452)------------------------------
% 1.64/0.57  % (2452)------------------------------
% 1.64/0.57  % (2437)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.64/0.58  % (2437)Refutation not found, incomplete strategy% (2437)------------------------------
% 1.64/0.58  % (2437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (2437)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (2437)Memory used [KB]: 11001
% 1.64/0.58  % (2437)Time elapsed: 0.162 s
% 1.64/0.58  % (2437)------------------------------
% 1.64/0.58  % (2437)------------------------------
% 1.64/0.64  % (2451)Refutation not found, incomplete strategy% (2451)------------------------------
% 1.64/0.64  % (2451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.64  % (2451)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.64  
% 1.64/0.64  % (2451)Memory used [KB]: 1663
% 1.64/0.64  % (2451)Time elapsed: 0.179 s
% 1.64/0.64  % (2451)------------------------------
% 1.64/0.64  % (2451)------------------------------
% 2.55/0.71  % (2430)Refutation not found, incomplete strategy% (2430)------------------------------
% 2.55/0.71  % (2430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.71  % (2430)Termination reason: Refutation not found, incomplete strategy
% 2.55/0.71  
% 2.55/0.71  % (2430)Memory used [KB]: 6780
% 2.55/0.71  % (2430)Time elapsed: 0.276 s
% 2.55/0.71  % (2430)------------------------------
% 2.55/0.71  % (2430)------------------------------
% 4.01/0.92  % (2436)Time limit reached!
% 4.01/0.92  % (2436)------------------------------
% 4.01/0.92  % (2436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.92  % (2436)Termination reason: Time limit
% 4.01/0.92  % (2436)Termination phase: Saturation
% 4.01/0.92  
% 4.01/0.92  % (2436)Memory used [KB]: 12920
% 4.01/0.92  % (2436)Time elapsed: 0.500 s
% 4.01/0.92  % (2436)------------------------------
% 4.01/0.92  % (2436)------------------------------
% 4.69/0.96  % (2441)Time limit reached!
% 4.69/0.96  % (2441)------------------------------
% 4.69/0.96  % (2441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.69/0.96  % (2441)Termination reason: Time limit
% 4.69/0.96  % (2441)Termination phase: Saturation
% 4.69/0.96  
% 4.69/0.96  % (2441)Memory used [KB]: 20340
% 4.69/0.96  % (2441)Time elapsed: 0.500 s
% 4.69/0.96  % (2441)------------------------------
% 4.69/0.96  % (2441)------------------------------
% 13.73/2.12  % (2443)Refutation found. Thanks to Tanya!
% 13.73/2.12  % SZS status Theorem for theBenchmark
% 13.73/2.12  % SZS output start Proof for theBenchmark
% 13.73/2.13  fof(f65061,plain,(
% 13.73/2.13    $false),
% 13.73/2.13    inference(global_subsumption,[],[f4809,f65060])).
% 13.73/2.13  fof(f65060,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f52601,f64896])).
% 13.73/2.13  fof(f64896,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f19115,f64890])).
% 13.73/2.13  fof(f64890,plain,(
% 13.73/2.13    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f47629,f64693])).
% 13.73/2.13  fof(f64693,plain,(
% 13.73/2.13    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f5733,f64686])).
% 13.73/2.13  fof(f64686,plain,(
% 13.73/2.13    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f55433,f64597])).
% 13.73/2.13  fof(f64597,plain,(
% 13.73/2.13    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 13.73/2.13    inference(backward_demodulation,[],[f19106,f64592])).
% 13.73/2.13  fof(f64592,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f51385,f64591])).
% 13.73/2.13  fof(f64591,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f64590,f10682])).
% 13.73/2.13  fof(f10682,plain,(
% 13.73/2.13    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f10510,f10679])).
% 13.73/2.13  fof(f10679,plain,(
% 13.73/2.13    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f10530,f10678])).
% 13.73/2.13  fof(f10678,plain,(
% 13.73/2.13    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f10474,f8286])).
% 13.73/2.13  fof(f8286,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f8285,f3774])).
% 13.73/2.13  fof(f3774,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f134,f122])).
% 13.73/2.13  fof(f122,plain,(
% 13.73/2.13    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f46])).
% 13.73/2.13  fof(f46,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f45])).
% 13.73/2.13  fof(f45,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f13])).
% 13.73/2.13  fof(f13,axiom,(
% 13.73/2.13    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 13.73/2.13  fof(f134,plain,(
% 13.73/2.13    m1_subset_1(sK9(sK0),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f83,f108])).
% 13.73/2.13  fof(f108,plain,(
% 13.73/2.13    ( ! [X0] : (m1_subset_1(sK9(X0),u1_struct_0(X0)) | v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f68])).
% 13.73/2.13  fof(f68,plain,(
% 13.73/2.13    ! [X0] : (((v11_lattices(X0) | (((k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f64,f67,f66,f65])).
% 13.73/2.13  fof(f65,plain,(
% 13.73/2.13    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f66,plain,(
% 13.73/2.13    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),X2),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f67,plain,(
% 13.73/2.13    ! [X0] : (? [X3] : (k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),X3)) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),X3)) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f64,plain,(
% 13.73/2.13    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k2_lattices(X0,X4,X5),k2_lattices(X0,X4,X6)) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(rectify,[],[f63])).
% 13.73/2.13  fof(f63,plain,(
% 13.73/2.13    ! [X0] : (((v11_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v11_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(nnf_transformation,[],[f32])).
% 13.73/2.13  fof(f32,plain,(
% 13.73/2.13    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f31])).
% 13.73/2.13  fof(f31,plain,(
% 13.73/2.13    ! [X0] : ((v11_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f4])).
% 13.73/2.13  fof(f4,axiom,(
% 13.73/2.13    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v11_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)))))))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).
% 13.73/2.13  fof(f83,plain,(
% 13.73/2.13    ~v11_lattices(sK0)),
% 13.73/2.13    inference(cnf_transformation,[],[f50])).
% 13.73/2.13  fof(f50,plain,(
% 13.73/2.13    ~v11_lattices(sK0) & ! [X1] : (! [X2] : (! [X3] : (k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 13.73/2.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f49])).
% 13.73/2.13  fof(f49,plain,(
% 13.73/2.13    ? [X0] : (~v11_lattices(X0) & ! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) = k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (~v11_lattices(sK0) & ! [X1] : (! [X2] : (! [X3] : (k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f19,plain,(
% 13.73/2.13    ? [X0] : (~v11_lattices(X0) & ! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) = k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f18])).
% 13.73/2.13  fof(f18,plain,(
% 13.73/2.13    ? [X0] : ((~v11_lattices(X0) & ! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) = k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f17])).
% 13.73/2.13  fof(f17,negated_conjecture,(
% 13.73/2.13    ~! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) = k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1))))) => v11_lattices(X0)))),
% 13.73/2.13    inference(negated_conjecture,[],[f16])).
% 13.73/2.13  fof(f16,conjecture,(
% 13.73/2.13    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,X2,X3)),k4_lattices(X0,X3,X1)) = k4_lattices(X0,k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X2,X3)),k3_lattices(X0,X3,X1))))) => v11_lattices(X0)))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_lattices)).
% 13.73/2.13  fof(f81,plain,(
% 13.73/2.13    l3_lattices(sK0)),
% 13.73/2.13    inference(cnf_transformation,[],[f50])).
% 13.73/2.13  fof(f132,plain,(
% 13.73/2.13    m1_subset_1(sK7(sK0),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f83,f106])).
% 13.73/2.13  fof(f106,plain,(
% 13.73/2.13    ( ! [X0] : (m1_subset_1(sK7(X0),u1_struct_0(X0)) | v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f68])).
% 13.73/2.13  fof(f124,plain,(
% 13.73/2.13    l1_lattices(sK0)),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f81,f84])).
% 13.73/2.13  fof(f84,plain,(
% 13.73/2.13    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f20])).
% 13.73/2.13  fof(f20,plain,(
% 13.73/2.13    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 13.73/2.13    inference(ennf_transformation,[],[f11])).
% 13.73/2.13  fof(f11,axiom,(
% 13.73/2.13    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 13.73/2.13  fof(f128,plain,(
% 13.73/2.13    v6_lattices(sK0)),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f81,f79,f80,f89])).
% 13.73/2.13  fof(f89,plain,(
% 13.73/2.13    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f22])).
% 13.73/2.13  fof(f22,plain,(
% 13.73/2.13    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 13.73/2.13    inference(flattening,[],[f21])).
% 13.73/2.13  fof(f21,plain,(
% 13.73/2.13    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 13.73/2.13    inference(ennf_transformation,[],[f1])).
% 13.73/2.13  fof(f1,axiom,(
% 13.73/2.13    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 13.73/2.13  fof(f80,plain,(
% 13.73/2.13    v10_lattices(sK0)),
% 13.73/2.13    inference(cnf_transformation,[],[f50])).
% 13.73/2.13  fof(f79,plain,(
% 13.73/2.13    ~v2_struct_0(sK0)),
% 13.73/2.13    inference(cnf_transformation,[],[f50])).
% 13.73/2.13  fof(f8285,plain,(
% 13.73/2.13    k2_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f8284,f4475])).
% 13.73/2.13  fof(f4475,plain,(
% 13.73/2.13    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3767,f4115])).
% 13.73/2.13  fof(f4115,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f134,f123])).
% 13.73/2.13  fof(f123,plain,(
% 13.73/2.13    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f48])).
% 13.73/2.13  fof(f48,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f47])).
% 13.73/2.13  fof(f47,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f3])).
% 13.73/2.13  fof(f3,axiom,(
% 13.73/2.13    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 13.73/2.13  fof(f186,plain,(
% 13.73/2.13    m1_subset_1(k3_lattices(sK0,sK7(sK0),sK8(sK0)),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f133,f118])).
% 13.73/2.13  fof(f118,plain,(
% 13.73/2.13    ( ! [X2,X0,X1] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f38])).
% 13.73/2.13  fof(f38,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f37])).
% 13.73/2.13  fof(f37,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f9])).
% 13.73/2.13  fof(f9,axiom,(
% 13.73/2.13    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattices)).
% 13.73/2.13  fof(f133,plain,(
% 13.73/2.13    m1_subset_1(sK8(sK0),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f83,f107])).
% 13.73/2.13  fof(f107,plain,(
% 13.73/2.13    ( ! [X0] : (m1_subset_1(sK8(X0),u1_struct_0(X0)) | v11_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f68])).
% 13.73/2.13  fof(f125,plain,(
% 13.73/2.13    l2_lattices(sK0)),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f81,f85])).
% 13.73/2.13  fof(f85,plain,(
% 13.73/2.13    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f20])).
% 13.73/2.13  fof(f126,plain,(
% 13.73/2.13    v4_lattices(sK0)),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f81,f79,f80,f87])).
% 13.73/2.13  fof(f87,plain,(
% 13.73/2.13    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f22])).
% 13.73/2.13  fof(f3767,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f134,f122])).
% 13.73/2.13  fof(f8284,plain,(
% 13.73/2.13    k2_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f8056,f3144])).
% 13.73/2.13  fof(f3144,plain,(
% 13.73/2.13    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f424,f2833])).
% 13.73/2.13  fof(f2833,plain,(
% 13.73/2.13    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,sK7(sK0),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f133,f120])).
% 13.73/2.13  fof(f120,plain,(
% 13.73/2.13    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f42])).
% 13.73/2.13  fof(f42,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f41])).
% 13.73/2.13  fof(f41,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f12])).
% 13.73/2.13  fof(f12,axiom,(
% 13.73/2.13    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 13.73/2.13  fof(f424,plain,(
% 13.73/2.13    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f133,f110])).
% 13.73/2.13  fof(f110,plain,(
% 13.73/2.13    ( ! [X4,X0,X3] : (~l3_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f73])).
% 13.73/2.13  fof(f73,plain,(
% 13.73/2.13    ! [X0] : (((v9_lattices(X0) | ((sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),sK11(X0))) & m1_subset_1(sK11(X0),u1_struct_0(X0))) & m1_subset_1(sK10(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f70,f72,f71])).
% 13.73/2.13  fof(f71,plain,(
% 13.73/2.13    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK10(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f72,plain,(
% 13.73/2.13    ! [X0] : (? [X2] : (sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK10(X0) != k2_lattices(X0,sK10(X0),k1_lattices(X0,sK10(X0),sK11(X0))) & m1_subset_1(sK11(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f70,plain,(
% 13.73/2.13    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(rectify,[],[f69])).
% 13.73/2.13  fof(f69,plain,(
% 13.73/2.13    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(nnf_transformation,[],[f34])).
% 13.73/2.13  fof(f34,plain,(
% 13.73/2.13    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f33])).
% 13.73/2.13  fof(f33,plain,(
% 13.73/2.13    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f8])).
% 13.73/2.13  fof(f8,axiom,(
% 13.73/2.13    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 13.73/2.13  fof(f131,plain,(
% 13.73/2.13    v9_lattices(sK0)),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f81,f79,f80,f92])).
% 13.73/2.13  fof(f92,plain,(
% 13.73/2.13    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f22])).
% 13.73/2.13  fof(f8056,plain,(
% 13.73/2.13    k2_lattices(sK0,sK7(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f124,f129,f132,f186,f134,f98])).
% 13.73/2.13  fof(f98,plain,(
% 13.73/2.13    ( ! [X6,X4,X0,X5] : (~l1_lattices(X0) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_lattices(X0) | k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f62])).
% 13.73/2.13  fof(f62,plain,(
% 13.73/2.13    ! [X0] : (((v7_lattices(X0) | (((k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f58,f61,f60,f59])).
% 13.73/2.13  fof(f59,plain,(
% 13.73/2.13    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f60,plain,(
% 13.73/2.13    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f61,plain,(
% 13.73/2.13    ! [X0] : (? [X3] : (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),k2_lattices(X0,sK5(X0),sK6(X0))) != k2_lattices(X0,k2_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f58,plain,(
% 13.73/2.13    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(rectify,[],[f57])).
% 13.73/2.13  fof(f57,plain,(
% 13.73/2.13    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(nnf_transformation,[],[f26])).
% 13.73/2.13  fof(f26,plain,(
% 13.73/2.13    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f25])).
% 13.73/2.13  fof(f25,plain,(
% 13.73/2.13    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f6])).
% 13.73/2.13  fof(f6,axiom,(
% 13.73/2.13    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3))))))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_lattices)).
% 13.73/2.13  fof(f129,plain,(
% 13.73/2.13    v7_lattices(sK0)),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f81,f79,f80,f90])).
% 13.73/2.13  fof(f90,plain,(
% 13.73/2.13    ( ! [X0] : (v7_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f22])).
% 13.73/2.13  fof(f10474,plain,(
% 13.73/2.13    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f310,f114])).
% 13.73/2.13  fof(f114,plain,(
% 13.73/2.13    ( ! [X4,X0,X3] : (~l3_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f78])).
% 13.73/2.13  fof(f78,plain,(
% 13.73/2.13    ! [X0] : (((v8_lattices(X0) | ((sK13(X0) != k1_lattices(X0,k2_lattices(X0,sK12(X0),sK13(X0)),sK13(X0)) & m1_subset_1(sK13(X0),u1_struct_0(X0))) & m1_subset_1(sK12(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f75,f77,f76])).
% 13.73/2.13  fof(f76,plain,(
% 13.73/2.13    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK12(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK12(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f77,plain,(
% 13.73/2.13    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK12(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK13(X0) != k1_lattices(X0,k2_lattices(X0,sK12(X0),sK13(X0)),sK13(X0)) & m1_subset_1(sK13(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f75,plain,(
% 13.73/2.13    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(rectify,[],[f74])).
% 13.73/2.13  fof(f74,plain,(
% 13.73/2.13    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(nnf_transformation,[],[f36])).
% 13.73/2.13  fof(f36,plain,(
% 13.73/2.13    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f35])).
% 13.73/2.13  fof(f35,plain,(
% 13.73/2.13    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f7])).
% 13.73/2.13  fof(f7,axiom,(
% 13.73/2.13    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
% 13.73/2.13  fof(f310,plain,(
% 13.73/2.13    m1_subset_1(k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f186,f121])).
% 13.73/2.13  fof(f121,plain,(
% 13.73/2.13    ( ! [X2,X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f44])).
% 13.73/2.13  fof(f44,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f43])).
% 13.73/2.13  fof(f43,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f10])).
% 13.73/2.13  fof(f10,axiom,(
% 13.73/2.13    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).
% 13.73/2.13  fof(f130,plain,(
% 13.73/2.13    v8_lattices(sK0)),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f81,f79,f80,f91])).
% 13.73/2.13  fof(f91,plain,(
% 13.73/2.13    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f22])).
% 13.73/2.13  fof(f10530,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f310,f120])).
% 13.73/2.13  fof(f202,plain,(
% 13.73/2.13    m1_subset_1(k4_lattices(sK0,sK7(sK0),sK9(sK0)),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f134,f121])).
% 13.73/2.13  fof(f10510,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f310,f119])).
% 13.73/2.13  fof(f119,plain,(
% 13.73/2.13    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f40])).
% 13.73/2.13  fof(f40,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f39])).
% 13.73/2.13  fof(f39,plain,(
% 13.73/2.13    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f2])).
% 13.73/2.13  fof(f2,axiom,(
% 13.73/2.13    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 13.73/2.13  fof(f64590,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f64589,f4115])).
% 13.73/2.13  fof(f64589,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f64588,f18957])).
% 13.73/2.13  fof(f18957,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f18928,f8670])).
% 13.73/2.13  fof(f8670,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f8669,f4389])).
% 13.73/2.13  fof(f4389,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,sK9(sK0),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3752,f4122])).
% 13.73/2.13  fof(f4122,plain,(
% 13.73/2.13    k4_lattices(sK0,sK9(sK0),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f134,f123])).
% 13.73/2.13  fof(f3752,plain,(
% 13.73/2.13    k4_lattices(sK0,sK9(sK0),sK7(sK0)) = k2_lattices(sK0,sK9(sK0),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f132,f122])).
% 13.73/2.13  fof(f8669,plain,(
% 13.73/2.13    k2_lattices(sK0,sK9(sK0),sK7(sK0)) = k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f8668,f4677])).
% 13.73/2.13  fof(f4677,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3742,f4090])).
% 13.73/2.13  fof(f4090,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f132,f123])).
% 13.73/2.13  fof(f190,plain,(
% 13.73/2.13    m1_subset_1(k3_lattices(sK0,sK8(sK0),sK9(sK0)),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f134,f118])).
% 13.73/2.13  fof(f3742,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f132,f122])).
% 13.73/2.13  fof(f8668,plain,(
% 13.73/2.13    k2_lattices(sK0,sK9(sK0),sK7(sK0)) = k2_lattices(sK0,sK9(sK0),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f7887,f3014])).
% 13.73/2.13  fof(f3014,plain,(
% 13.73/2.13    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f426,f3013])).
% 13.73/2.13  fof(f3013,plain,(
% 13.73/2.13    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK9(sK0),sK8(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f2835,f2006])).
% 13.73/2.13  fof(f2006,plain,(
% 13.73/2.13    k3_lattices(sK0,sK9(sK0),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f134,f119])).
% 13.73/2.13  fof(f2835,plain,(
% 13.73/2.13    k3_lattices(sK0,sK9(sK0),sK8(sK0)) = k1_lattices(sK0,sK9(sK0),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f133,f120])).
% 13.73/2.13  fof(f426,plain,(
% 13.73/2.13    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k1_lattices(sK0,sK9(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f133,f110])).
% 13.73/2.13  fof(f7887,plain,(
% 13.73/2.13    k2_lattices(sK0,sK9(sK0),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f124,f129,f134,f190,f132,f98])).
% 13.73/2.13  fof(f18928,plain,(
% 13.73/2.13    k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f642,f122])).
% 13.73/2.13  fof(f642,plain,(
% 13.73/2.13    m1_subset_1(k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f190,f121])).
% 13.73/2.13  fof(f64588,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f64587,f18978])).
% 13.73/2.13  fof(f18978,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f18944,f18977])).
% 13.73/2.13  fof(f18977,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f18918,f8688])).
% 13.73/2.13  fof(f8688,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f8687,f4677])).
% 13.73/2.13  fof(f8687,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f8686,f8664])).
% 13.73/2.13  fof(f8664,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f8663,f4677])).
% 13.73/2.13  fof(f8663,plain,(
% 13.73/2.13    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f8662,f4674])).
% 13.73/2.13  fof(f4674,plain,(
% 13.73/2.13    sK7(sK0) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3743,f4672])).
% 13.73/2.13  fof(f4672,plain,(
% 13.73/2.13    sK7(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f4091,f3938])).
% 13.73/2.13  fof(f3938,plain,(
% 13.73/2.13    sK7(sK0) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f3666,f3144])).
% 13.73/2.13  fof(f3666,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f186,f122])).
% 13.73/2.13  fof(f4091,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f132,f123])).
% 13.73/2.13  fof(f3743,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f132,f122])).
% 13.73/2.13  fof(f8662,plain,(
% 13.73/2.13    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f7889,f4779])).
% 13.73/2.13  fof(f4779,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f3658,f4006])).
% 13.73/2.13  fof(f4006,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f186,f123])).
% 13.73/2.13  fof(f3658,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f186,f122])).
% 13.73/2.13  fof(f7889,plain,(
% 13.73/2.13    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f186,f132,f98])).
% 13.73/2.13  fof(f8686,plain,(
% 13.73/2.13    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f7881,f3647])).
% 13.73/2.13  fof(f3647,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f190,f122])).
% 13.73/2.13  fof(f7881,plain,(
% 13.73/2.13    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f124,f129,f186,f190,f132,f98])).
% 13.73/2.13  fof(f18918,plain,(
% 13.73/2.13    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f642,f122])).
% 13.73/2.13  fof(f18944,plain,(
% 13.73/2.13    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f642,f123])).
% 13.73/2.13  fof(f64587,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f64586,f55378])).
% 13.73/2.13  fof(f55378,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f51352,f55370])).
% 13.73/2.13  fof(f55370,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f53824,f55333])).
% 13.73/2.13  fof(f55333,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f50756,f55295])).
% 13.73/2.13  fof(f55295,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f55294,f52593])).
% 13.73/2.13  fof(f52593,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f50198,f52539])).
% 13.73/2.13  fof(f52539,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f50202,f52538])).
% 13.73/2.13  fof(f52538,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f52537,f1929])).
% 13.73/2.13  fof(f1929,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f202,f119])).
% 13.73/2.13  fof(f199,plain,(
% 13.73/2.13    m1_subset_1(k4_lattices(sK0,sK7(sK0),sK8(sK0)),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f133,f121])).
% 13.73/2.13  fof(f52537,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f52536,f38688])).
% 13.73/2.13  fof(f38688,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f38476,f8179])).
% 13.73/2.13  fof(f8179,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f3876,f8176])).
% 13.73/2.13  fof(f8176,plain,(
% 13.73/2.13    k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f8175,f8140])).
% 13.73/2.13  fof(f8140,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f8139,f3738])).
% 13.73/2.13  fof(f3738,plain,(
% 13.73/2.13    k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f203,f122])).
% 13.73/2.13  fof(f203,plain,(
% 13.73/2.13    m1_subset_1(k4_lattices(sK0,sK8(sK0),sK9(sK0)),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f134,f121])).
% 13.73/2.13  fof(f8139,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f8138,f3775])).
% 13.73/2.13  fof(f3775,plain,(
% 13.73/2.13    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f134,f122])).
% 13.73/2.13  fof(f8138,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,sK7(sK0),k2_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f8101,f3762])).
% 13.73/2.13  fof(f3762,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,sK7(sK0),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f133,f122])).
% 13.73/2.13  fof(f8101,plain,(
% 13.73/2.13    k2_lattices(sK0,sK7(sK0),k2_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f124,f129,f132,f133,f134,f98])).
% 13.73/2.13  fof(f8175,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f8174,f3727])).
% 13.73/2.13  fof(f3727,plain,(
% 13.73/2.13    k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f202,f122])).
% 13.73/2.13  fof(f8174,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f8173,f3774])).
% 13.73/2.13  fof(f8173,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f8093,f4568])).
% 13.73/2.13  fof(f4568,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,sK8(sK0),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3751,f4110])).
% 13.73/2.13  fof(f4110,plain,(
% 13.73/2.13    k4_lattices(sK0,sK8(sK0),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f133,f123])).
% 13.73/2.13  fof(f3751,plain,(
% 13.73/2.13    k4_lattices(sK0,sK8(sK0),sK7(sK0)) = k2_lattices(sK0,sK8(sK0),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f132,f122])).
% 13.73/2.13  fof(f8093,plain,(
% 13.73/2.13    k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK8(sK0),sK7(sK0)),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f124,f129,f133,f132,f134,f98])).
% 13.73/2.13  fof(f3876,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f1456,f3727])).
% 13.73/2.13  fof(f1456,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f202,f114])).
% 13.73/2.13  fof(f38476,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f1676,f120])).
% 13.73/2.13  fof(f1676,plain,(
% 13.73/2.13    m1_subset_1(k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f203,f121])).
% 13.73/2.13  fof(f52536,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f52535,f8145])).
% 13.73/2.13  fof(f8145,plain,(
% 13.73/2.13    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f4118,f8141])).
% 13.73/2.13  fof(f8141,plain,(
% 13.73/2.13    k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f4467,f8140])).
% 13.73/2.13  fof(f4467,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f3770,f4118])).
% 13.73/2.13  fof(f3770,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f134,f122])).
% 13.73/2.13  fof(f4118,plain,(
% 13.73/2.13    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f134,f123])).
% 13.73/2.13  fof(f52535,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f52534,f4122])).
% 13.73/2.13  fof(f52534,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f52533,f4664])).
% 13.73/2.13  fof(f4664,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f4094,f4624])).
% 13.73/2.13  fof(f4624,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3746,f4621])).
% 13.73/2.13  fof(f4621,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3309,f4618])).
% 13.73/2.13  fof(f4618,plain,(
% 13.73/2.13    sK7(sK0) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f3308,f4571])).
% 13.73/2.13  fof(f4571,plain,(
% 13.73/2.13    sK7(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3843,f4110])).
% 13.73/2.13  fof(f3843,plain,(
% 13.73/2.13    sK7(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK7(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f956,f3751])).
% 13.73/2.13  fof(f956,plain,(
% 13.73/2.13    sK7(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),sK7(sK0)),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f132,f114])).
% 13.73/2.13  fof(f3308,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f2814,f1965])).
% 13.73/2.13  fof(f1965,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f132,f119])).
% 13.73/2.13  fof(f2814,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f132,f120])).
% 13.73/2.13  fof(f3309,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f1136,f3308])).
% 13.73/2.13  fof(f1136,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f199,f110])).
% 13.73/2.13  fof(f3746,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f132,f122])).
% 13.73/2.13  fof(f4094,plain,(
% 13.73/2.13    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f132,f123])).
% 13.73/2.13  fof(f52533,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f52532,f23066])).
% 13.73/2.13  fof(f23066,plain,(
% 13.73/2.13    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f22863,f23061])).
% 13.73/2.13  fof(f23061,plain,(
% 13.73/2.13    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f22890,f23060])).
% 13.73/2.13  fof(f23060,plain,(
% 13.73/2.13    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f22661,f6084])).
% 13.73/2.13  fof(f6084,plain,(
% 13.73/2.13    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f6083,f5644])).
% 13.73/2.13  fof(f5644,plain,(
% 13.73/2.13    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f5643,f2848])).
% 13.73/2.13  fof(f2848,plain,(
% 13.73/2.13    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,sK7(sK0),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f134,f120])).
% 13.73/2.13  fof(f5643,plain,(
% 13.73/2.13    k1_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f5517,f4571])).
% 13.73/2.13  fof(f5517,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f132,f134,f93])).
% 13.73/2.13  fof(f93,plain,(
% 13.73/2.13    ( ! [X6,X4,X0,X5] : (~l2_lattices(X0) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_lattices(X0) | k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | v2_struct_0(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f56])).
% 13.73/2.13  fof(f56,plain,(
% 13.73/2.13    ! [X0] : (((v5_lattices(X0) | (((k1_lattices(X0,sK1(X0),k1_lattices(X0,sK2(X0),sK3(X0))) != k1_lattices(X0,k1_lattices(X0,sK1(X0),sK2(X0)),sK3(X0)) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f52,f55,f54,f53])).
% 13.73/2.13  fof(f53,plain,(
% 13.73/2.13    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_lattices(X0,sK1(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK1(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f54,plain,(
% 13.73/2.13    ! [X0] : (? [X2] : (? [X3] : (k1_lattices(X0,sK1(X0),k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,sK1(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k1_lattices(X0,sK1(X0),k1_lattices(X0,sK2(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK1(X0),sK2(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f55,plain,(
% 13.73/2.13    ! [X0] : (? [X3] : (k1_lattices(X0,sK1(X0),k1_lattices(X0,sK2(X0),X3)) != k1_lattices(X0,k1_lattices(X0,sK1(X0),sK2(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_lattices(X0,sK1(X0),k1_lattices(X0,sK2(X0),sK3(X0))) != k1_lattices(X0,k1_lattices(X0,sK1(X0),sK2(X0)),sK3(X0)) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 13.73/2.13    introduced(choice_axiom,[])).
% 13.73/2.13  fof(f52,plain,(
% 13.73/2.13    ! [X0] : (((v5_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(rectify,[],[f51])).
% 13.73/2.13  fof(f51,plain,(
% 13.73/2.13    ! [X0] : (((v5_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v5_lattices(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(nnf_transformation,[],[f24])).
% 13.73/2.13  fof(f24,plain,(
% 13.73/2.13    ! [X0] : ((v5_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 13.73/2.13    inference(flattening,[],[f23])).
% 13.73/2.13  fof(f23,plain,(
% 13.73/2.13    ! [X0] : ((v5_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 13.73/2.13    inference(ennf_transformation,[],[f5])).
% 13.73/2.13  fof(f5,axiom,(
% 13.73/2.13    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => (v5_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3))))))),
% 13.73/2.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattices)).
% 13.73/2.13  fof(f127,plain,(
% 13.73/2.13    v5_lattices(sK0)),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f81,f79,f80,f88])).
% 13.73/2.13  fof(f88,plain,(
% 13.73/2.13    ( ! [X0] : (v5_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 13.73/2.13    inference(cnf_transformation,[],[f22])).
% 13.73/2.13  fof(f6083,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f6082,f3171])).
% 13.73/2.13  fof(f3171,plain,(
% 13.73/2.13    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,sK9(sK0),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f2820,f2005])).
% 13.73/2.13  fof(f2005,plain,(
% 13.73/2.13    k3_lattices(sK0,sK9(sK0),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f134,f119])).
% 13.73/2.13  fof(f2820,plain,(
% 13.73/2.13    k3_lattices(sK0,sK9(sK0),sK7(sK0)) = k1_lattices(sK0,sK9(sK0),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f132,f120])).
% 13.73/2.13  fof(f6082,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f5373,f2995])).
% 13.73/2.13  fof(f2995,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f2844,f2001])).
% 13.73/2.13  fof(f2001,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f134,f119])).
% 13.73/2.13  fof(f2844,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f134,f120])).
% 13.73/2.13  fof(f5373,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f134,f132,f93])).
% 13.73/2.13  fof(f22661,plain,(
% 13.73/2.13    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f1213,f110])).
% 13.73/2.13  fof(f1213,plain,(
% 13.73/2.13    m1_subset_1(k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f199,f118])).
% 13.73/2.13  fof(f22890,plain,(
% 13.73/2.13    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f22821,f22863])).
% 13.73/2.13  fof(f22821,plain,(
% 13.73/2.13    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f1213,f122])).
% 13.73/2.13  fof(f189,plain,(
% 13.73/2.13    m1_subset_1(k3_lattices(sK0,sK7(sK0),sK9(sK0)),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f134,f118])).
% 13.73/2.13  fof(f22863,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f1213,f123])).
% 13.73/2.13  fof(f52532,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f52531,f2001])).
% 13.73/2.13  fof(f52531,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f52530,f2005])).
% 13.73/2.13  fof(f52530,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK7(sK0))),sK7(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f46573,f4618])).
% 13.73/2.13  fof(f46573,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK7(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f199,f134,f132,f82])).
% 13.73/2.13  fof(f82,plain,(
% 13.73/2.13    ( ! [X2,X3,X1] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,X1,X2),k4_lattices(sK0,X2,X3)),k4_lattices(sK0,X3,X1)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,X1,X2),k3_lattices(sK0,X2,X3)),k3_lattices(sK0,X3,X1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 13.73/2.13    inference(cnf_transformation,[],[f50])).
% 13.73/2.13  fof(f50202,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f22871,f50199])).
% 13.73/2.13  fof(f50199,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f47596,f50198])).
% 13.73/2.13  fof(f47596,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f47595,f4624])).
% 13.73/2.13  fof(f47595,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f47594,f8141])).
% 13.73/2.13  fof(f47594,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f47593,f3966])).
% 13.73/2.13  fof(f3966,plain,(
% 13.73/2.13    sK7(sK0) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f3642,f2986])).
% 13.73/2.13  fof(f2986,plain,(
% 13.73/2.13    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f432,f2848])).
% 13.73/2.13  fof(f432,plain,(
% 13.73/2.13    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f134,f110])).
% 13.73/2.13  fof(f3642,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f189,f122])).
% 13.73/2.13  fof(f47593,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f47117,f4622])).
% 13.73/2.13  fof(f4622,plain,(
% 13.73/2.13    sK7(sK0) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f1965,f4618])).
% 13.73/2.13  fof(f47117,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f199,f132,f134,f82])).
% 13.73/2.13  fof(f22871,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f1213,f123])).
% 13.73/2.13  fof(f50198,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f50197,f1929])).
% 13.73/2.13  fof(f50197,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f50196,f4451])).
% 13.73/2.13  fof(f4451,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3748,f4448])).
% 13.73/2.13  fof(f4448,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3305,f4445])).
% 13.73/2.13  fof(f4445,plain,(
% 13.73/2.13    sK7(sK0) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(backward_demodulation,[],[f3304,f4394])).
% 13.73/2.13  fof(f4394,plain,(
% 13.73/2.13    sK7(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3835,f4122])).
% 13.73/2.13  fof(f3835,plain,(
% 13.73/2.13    sK7(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),sK7(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f957,f3752])).
% 13.73/2.13  fof(f957,plain,(
% 13.73/2.13    sK7(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),sK7(sK0)),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f132,f114])).
% 13.73/2.13  fof(f3304,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f2816,f1967])).
% 13.73/2.13  fof(f1967,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f132,f119])).
% 13.73/2.13  fof(f2816,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f132,f120])).
% 13.73/2.13  fof(f3305,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f1404,f3304])).
% 13.73/2.13  fof(f1404,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f202,f110])).
% 13.73/2.13  fof(f3748,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f132,f122])).
% 13.73/2.13  fof(f50196,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f50195,f8176])).
% 13.73/2.13  fof(f50195,plain,(
% 13.73/2.13    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f50194,f3938])).
% 13.73/2.13  fof(f50194,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f46829,f4449])).
% 13.73/2.13  fof(f4449,plain,(
% 13.73/2.13    sK7(sK0) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f1967,f4445])).
% 13.73/2.13  fof(f46829,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f202,f132,f133,f82])).
% 13.73/2.13  fof(f55294,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f55293,f52542])).
% 13.73/2.13  fof(f52542,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f27421,f52539])).
% 13.73/2.13  fof(f27421,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f1490,f123])).
% 13.73/2.13  fof(f1490,plain,(
% 13.73/2.13    m1_subset_1(k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),u1_struct_0(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f202,f118])).
% 13.73/2.13  fof(f55293,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f55292,f27594])).
% 13.73/2.13  fof(f27594,plain,(
% 13.73/2.13    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f27386,f27593])).
% 13.73/2.13  fof(f27593,plain,(
% 13.73/2.13    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f27206,f5999])).
% 13.73/2.13  fof(f5999,plain,(
% 13.73/2.13    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(forward_demodulation,[],[f5998,f3149])).
% 13.73/2.13  fof(f3149,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f2831,f1985])).
% 13.73/2.13  fof(f1985,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f133,f119])).
% 13.73/2.13  fof(f2831,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f133,f120])).
% 13.73/2.13  fof(f5998,plain,(
% 13.73/2.13    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f5997,f5981])).
% 13.73/2.13  fof(f5981,plain,(
% 13.73/2.13    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f5980,f3149])).
% 13.73/2.13  fof(f5980,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f5979,f4235])).
% 13.73/2.13  fof(f4235,plain,(
% 13.73/2.13    sK8(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f3807,f4123])).
% 13.73/2.13  fof(f4123,plain,(
% 13.73/2.13    k4_lattices(sK0,sK9(sK0),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),sK9(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f134,f123])).
% 13.73/2.13  fof(f3807,plain,(
% 13.73/2.13    sK8(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),sK8(sK0)),sK8(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f970,f3764])).
% 13.73/2.13  fof(f3764,plain,(
% 13.73/2.13    k4_lattices(sK0,sK9(sK0),sK8(sK0)) = k2_lattices(sK0,sK9(sK0),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f133,f122])).
% 13.73/2.13  fof(f970,plain,(
% 13.73/2.13    sK8(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),sK8(sK0)),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f133,f114])).
% 13.73/2.13  fof(f5979,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f5416,f2801])).
% 13.73/2.13  fof(f2801,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f203,f120])).
% 13.73/2.13  fof(f5416,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f203,f133,f93])).
% 13.73/2.13  fof(f5997,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f5408,f3347])).
% 13.73/2.13  fof(f3347,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f2787,f1949])).
% 13.73/2.13  fof(f1949,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f203,f119])).
% 13.73/2.13  fof(f2787,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f202,f120])).
% 13.73/2.13  fof(f5408,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f202,f133,f93])).
% 13.73/2.13  fof(f27206,plain,(
% 13.73/2.13    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f81,f131,f203,f1490,f110])).
% 13.73/2.13  fof(f27386,plain,(
% 13.73/2.13    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f1490,f122])).
% 13.73/2.13  fof(f55292,plain,(
% 13.73/2.13    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 13.73/2.13    inference(forward_demodulation,[],[f55291,f32858])).
% 13.73/2.13  fof(f32858,plain,(
% 13.73/2.13    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 13.73/2.13    inference(backward_demodulation,[],[f32669,f32857])).
% 13.73/2.13  fof(f32857,plain,(
% 13.73/2.13    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f32408,f5967])).
% 13.73/2.13  fof(f5967,plain,(
% 13.73/2.13    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(backward_demodulation,[],[f5913,f5959])).
% 13.73/2.13  fof(f5959,plain,(
% 13.73/2.13    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f5958,f2833])).
% 13.73/2.13  fof(f5958,plain,(
% 13.73/2.13    k1_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f5957,f4235])).
% 13.73/2.13  fof(f5957,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f5956,f5913])).
% 13.73/2.13  fof(f5956,plain,(
% 13.73/2.13    k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f5419,f2803])).
% 13.73/2.13  fof(f2803,plain,(
% 13.73/2.13    k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f203,f120])).
% 13.73/2.13  fof(f5419,plain,(
% 13.73/2.13    k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f125,f127,f132,f203,f133,f93])).
% 13.73/2.13  fof(f5913,plain,(
% 13.73/2.13    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f5912,f3571])).
% 13.73/2.13  fof(f3571,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f2652,f1939])).
% 13.73/2.13  fof(f1939,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f203,f119])).
% 13.73/2.13  fof(f2652,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f186,f120])).
% 13.73/2.13  fof(f5912,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f5911,f2833])).
% 13.73/2.13  fof(f5911,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 13.73/2.13    inference(forward_demodulation,[],[f5435,f3302])).
% 13.73/2.13  fof(f3302,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(forward_demodulation,[],[f2817,f1968])).
% 13.73/2.13  fof(f1968,plain,(
% 13.73/2.13    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f132,f119])).
% 13.73/2.13  fof(f2817,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f132,f120])).
% 13.73/2.13  fof(f5435,plain,(
% 13.73/2.13    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),sK8(sK0))),
% 13.73/2.13    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f132,f133,f93])).
% 14.18/2.14  fof(f32408,plain,(
% 14.18/2.14    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f1640,f110])).
% 14.18/2.14  fof(f1640,plain,(
% 14.18/2.14    m1_subset_1(k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),u1_struct_0(sK0))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f203,f118])).
% 14.18/2.14  fof(f32669,plain,(
% 14.18/2.14    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f32590,f32638])).
% 14.18/2.14  fof(f32638,plain,(
% 14.18/2.14    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f1640,f123])).
% 14.18/2.14  fof(f32590,plain,(
% 14.18/2.14    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f1640,f122])).
% 14.18/2.14  fof(f55291,plain,(
% 14.18/2.14    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f55290,f27476])).
% 14.18/2.14  fof(f27476,plain,(
% 14.18/2.14    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f27316,f6112])).
% 14.18/2.14  fof(f6112,plain,(
% 14.18/2.14    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f6111,f5915])).
% 14.18/2.14  fof(f5915,plain,(
% 14.18/2.14    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.14    inference(forward_demodulation,[],[f5914,f2833])).
% 14.18/2.14  fof(f5914,plain,(
% 14.18/2.14    k1_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.14    inference(forward_demodulation,[],[f5434,f4394])).
% 14.18/2.14  fof(f5434,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),sK8(sK0))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f132,f133,f93])).
% 14.18/2.14  fof(f6111,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f6110,f3175])).
% 14.18/2.14  fof(f3175,plain,(
% 14.18/2.14    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,sK8(sK0),sK7(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f2819,f1987])).
% 14.18/2.14  fof(f1987,plain,(
% 14.18/2.14    k3_lattices(sK0,sK8(sK0),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),sK8(sK0))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f133,f119])).
% 14.18/2.14  fof(f2819,plain,(
% 14.18/2.14    k3_lattices(sK0,sK8(sK0),sK7(sK0)) = k1_lattices(sK0,sK8(sK0),sK7(sK0))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f132,f120])).
% 14.18/2.14  fof(f6110,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f5362,f3149])).
% 14.18/2.14  fof(f5362,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),sK7(sK0))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f133,f132,f93])).
% 14.18/2.14  fof(f27316,plain,(
% 14.18/2.14    k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f1490,f120])).
% 14.18/2.14  fof(f55290,plain,(
% 14.18/2.14    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f46241,f27467])).
% 14.18/2.14  fof(f27467,plain,(
% 14.18/2.14    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f27326,f5999])).
% 14.18/2.14  fof(f27326,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f1490,f120])).
% 14.18/2.14  fof(f46241,plain,(
% 14.18/2.14    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f1490,f132,f203,f82])).
% 14.18/2.14  fof(f50756,plain,(
% 14.18/2.14    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.14    inference(backward_demodulation,[],[f50737,f50755])).
% 14.18/2.14  fof(f50755,plain,(
% 14.18/2.14    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f50754,f38701])).
% 14.18/2.14  fof(f38701,plain,(
% 14.18/2.14    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f38459,f38688])).
% 14.18/2.14  fof(f38459,plain,(
% 14.18/2.14    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f1676,f119])).
% 14.18/2.14  fof(f50754,plain,(
% 14.18/2.14    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f50753,f23040])).
% 14.18/2.14  fof(f23040,plain,(
% 14.18/2.14    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.14    inference(backward_demodulation,[],[f22865,f23035])).
% 14.18/2.14  fof(f23035,plain,(
% 14.18/2.14    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.14    inference(backward_demodulation,[],[f22837,f23034])).
% 14.18/2.14  fof(f23034,plain,(
% 14.18/2.14    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f22669,f5767])).
% 14.18/2.14  fof(f5767,plain,(
% 14.18/2.14    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.14    inference(backward_demodulation,[],[f5703,f5766])).
% 14.18/2.14  fof(f5766,plain,(
% 14.18/2.14    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f5765,f2995])).
% 14.18/2.14  fof(f5765,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f5764,f3788])).
% 14.18/2.14  fof(f3788,plain,(
% 14.18/2.14    sK9(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.14    inference(backward_demodulation,[],[f981,f3774])).
% 14.18/2.14  fof(f981,plain,(
% 14.18/2.14    sK9(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f134,f114])).
% 14.18/2.14  fof(f5764,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f5490,f2784])).
% 14.18/2.14  fof(f2784,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f202,f120])).
% 14.18/2.14  fof(f5490,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f202,f134,f93])).
% 14.18/2.14  fof(f5703,plain,(
% 14.18/2.14    k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f5702,f2995])).
% 14.18/2.14  fof(f5702,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f5506,f3385])).
% 14.18/2.14  fof(f3385,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.14    inference(forward_demodulation,[],[f2756,f1929])).
% 14.18/2.14  fof(f2756,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f199,f120])).
% 14.18/2.14  fof(f5506,plain,(
% 14.18/2.14    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f199,f134,f93])).
% 14.18/2.14  fof(f22669,plain,(
% 14.18/2.14    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f81,f131,f202,f1213,f110])).
% 14.18/2.14  fof(f22837,plain,(
% 14.18/2.14    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f1213,f122])).
% 14.18/2.14  fof(f22865,plain,(
% 14.18/2.14    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f1213,f123])).
% 14.18/2.14  fof(f50753,plain,(
% 14.18/2.14    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f50752,f8180])).
% 14.18/2.14  fof(f8180,plain,(
% 14.18/2.14    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.14    inference(backward_demodulation,[],[f4108,f8176])).
% 14.18/2.14  fof(f4108,plain,(
% 14.18/2.14    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f133,f123])).
% 14.18/2.14  fof(f50752,plain,(
% 14.18/2.14    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.14    inference(forward_demodulation,[],[f50751,f49791])).
% 14.18/2.14  fof(f49791,plain,(
% 14.18/2.14    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.14    inference(backward_demodulation,[],[f22872,f49790])).
% 14.18/2.14  fof(f49790,plain,(
% 14.18/2.14    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f49789,f1947])).
% 14.18/2.14  fof(f1947,plain,(
% 14.18/2.14    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f203,f119])).
% 14.18/2.14  fof(f49789,plain,(
% 14.18/2.14    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.14    inference(forward_demodulation,[],[f49788,f38687])).
% 14.18/2.14  fof(f38687,plain,(
% 14.18/2.14    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.14    inference(forward_demodulation,[],[f38477,f3865])).
% 14.18/2.14  fof(f3865,plain,(
% 14.18/2.14    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.14    inference(backward_demodulation,[],[f1604,f3738])).
% 14.18/2.14  fof(f1604,plain,(
% 14.18/2.14    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.14    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f203,f114])).
% 14.18/2.15  fof(f38477,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f1676,f120])).
% 14.18/2.15  fof(f49788,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f49787,f8145])).
% 14.18/2.15  fof(f49787,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f49786,f4123])).
% 14.18/2.15  fof(f49786,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f49785,f4638])).
% 14.18/2.15  fof(f4638,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f4106,f3828])).
% 14.18/2.15  fof(f3828,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f3758,f3820])).
% 14.18/2.15  fof(f3820,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f3154,f3817])).
% 14.18/2.15  fof(f3817,plain,(
% 14.18/2.15    sK8(sK0) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3153,f3816])).
% 14.18/2.15  fof(f3816,plain,(
% 14.18/2.15    sK8(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f968,f3762])).
% 14.18/2.15  fof(f968,plain,(
% 14.18/2.15    sK8(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f133,f114])).
% 14.18/2.15  fof(f3153,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2829,f1983])).
% 14.18/2.15  fof(f1983,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f133,f119])).
% 14.18/2.15  fof(f2829,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f133,f120])).
% 14.18/2.15  fof(f3154,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f1137,f3153])).
% 14.18/2.15  fof(f1137,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f199,f110])).
% 14.18/2.15  fof(f3758,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f133,f122])).
% 14.18/2.15  fof(f4106,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f133,f123])).
% 14.18/2.15  fof(f49785,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49784,f23059])).
% 14.18/2.15  fof(f23059,plain,(
% 14.18/2.15    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f22864,f23054])).
% 14.18/2.15  fof(f23054,plain,(
% 14.18/2.15    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f22889,f23053])).
% 14.18/2.15  fof(f23053,plain,(
% 14.18/2.15    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f22662,f5854])).
% 14.18/2.15  fof(f5854,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5853,f5575])).
% 14.18/2.15  fof(f5575,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5574,f2849])).
% 14.18/2.15  fof(f2849,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f134,f120])).
% 14.18/2.15  fof(f5574,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5526,f3816])).
% 14.18/2.15  fof(f5526,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f133,f134,f93])).
% 14.18/2.15  fof(f5853,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5852,f3013])).
% 14.18/2.15  fof(f5852,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5454,f2995])).
% 14.18/2.15  fof(f5454,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f134,f133,f93])).
% 14.18/2.15  fof(f22662,plain,(
% 14.18/2.15    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f1213,f110])).
% 14.18/2.15  fof(f22889,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f22822,f22864])).
% 14.18/2.15  fof(f22822,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f1213,f122])).
% 14.18/2.15  fof(f22864,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f1213,f123])).
% 14.18/2.15  fof(f49784,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f49783,f2001])).
% 14.18/2.15  fof(f49783,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f49782,f2006])).
% 14.18/2.15  fof(f49782,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f46862,f3817])).
% 14.18/2.15  fof(f46862,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f199,f134,f133,f82])).
% 14.18/2.15  fof(f22872,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f1213,f123])).
% 14.18/2.15  fof(f50751,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f50750,f49378])).
% 14.18/2.15  fof(f49378,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f48143,f49327])).
% 14.18/2.15  fof(f49327,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49326,f49201])).
% 14.18/2.15  fof(f49201,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49200,f32823])).
% 14.18/2.15  fof(f32823,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f32611,f32822])).
% 14.18/2.15  fof(f32822,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f32419,f6167])).
% 14.18/2.15  fof(f6167,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f6166,f3302])).
% 14.18/2.15  fof(f6166,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f6165,f6149])).
% 14.18/2.15  fof(f6149,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f6148,f3302])).
% 14.18/2.15  fof(f6148,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f6147,f4571])).
% 14.18/2.15  fof(f6147,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5345,f3383])).
% 14.18/2.15  fof(f3383,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2757,f1947])).
% 14.18/2.15  fof(f2757,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f199,f120])).
% 14.18/2.15  fof(f5345,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f199,f132,f93])).
% 14.18/2.15  fof(f6165,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5337,f2799])).
% 14.18/2.15  fof(f2799,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f203,f120])).
% 14.18/2.15  fof(f5337,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f203,f132,f93])).
% 14.18/2.15  fof(f32419,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f199,f1640,f110])).
% 14.18/2.15  fof(f32611,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f1640,f122])).
% 14.18/2.15  fof(f49200,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49199,f47524])).
% 14.18/2.15  fof(f47524,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47523,f38688])).
% 14.18/2.15  fof(f47523,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f47522,f4097])).
% 14.18/2.15  fof(f4097,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f132,f123])).
% 14.18/2.15  fof(f47522,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f47521,f4456])).
% 14.18/2.15  fof(f4456,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f4121,f3796])).
% 14.18/2.15  fof(f3796,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f3773,f3784])).
% 14.18/2.15  fof(f3784,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f2990,f3781])).
% 14.18/2.15  fof(f3781,plain,(
% 14.18/2.15    sK9(sK0) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f2989,f3780])).
% 14.18/2.15  fof(f3780,plain,(
% 14.18/2.15    sK9(sK0) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f982,f3775])).
% 14.18/2.15  fof(f982,plain,(
% 14.18/2.15    sK9(sK0) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f134,f114])).
% 14.18/2.15  fof(f2989,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2847,f2004])).
% 14.18/2.15  fof(f2004,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f134,f119])).
% 14.18/2.15  fof(f2847,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f134,f120])).
% 14.18/2.15  fof(f2990,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f1552,f2989])).
% 14.18/2.15  fof(f1552,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f203,f110])).
% 14.18/2.15  fof(f3773,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f134,f122])).
% 14.18/2.15  fof(f4121,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f134,f123])).
% 14.18/2.15  fof(f47521,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f47520,f32850])).
% 14.18/2.15  fof(f32850,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f32639,f32845])).
% 14.18/2.15  fof(f32845,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f32668,f32844])).
% 14.18/2.15  fof(f32844,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f32409,f5724])).
% 14.18/2.15  fof(f5724,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f5659,f5717])).
% 14.18/2.15  fof(f5717,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5716,f2848])).
% 14.18/2.15  fof(f5716,plain,(
% 14.18/2.15    k1_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5715,f3780])).
% 14.18/2.15  fof(f5715,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5714,f5659])).
% 14.18/2.15  fof(f5714,plain,(
% 14.18/2.15    k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5500,f2803])).
% 14.18/2.15  fof(f5500,plain,(
% 14.18/2.15    k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f132,f203,f134,f93])).
% 14.18/2.15  fof(f5659,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5658,f3508])).
% 14.18/2.15  fof(f3508,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2682,f1942])).
% 14.18/2.15  fof(f1942,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f203,f119])).
% 14.18/2.15  fof(f2682,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f189,f120])).
% 14.18/2.15  fof(f5658,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5657,f2848])).
% 14.18/2.15  fof(f5657,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5516,f3302])).
% 14.18/2.15  fof(f5516,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f132,f134,f93])).
% 14.18/2.15  fof(f32409,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f1640,f110])).
% 14.18/2.15  fof(f32668,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f32591,f32639])).
% 14.18/2.15  fof(f32591,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f1640,f122])).
% 14.18/2.15  fof(f32639,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f1640,f123])).
% 14.18/2.15  fof(f47520,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47519,f1968])).
% 14.18/2.15  fof(f47519,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47119,f3781])).
% 14.18/2.15  fof(f47119,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f203,f132,f134,f82])).
% 14.18/2.15  fof(f49199,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49198,f8141])).
% 14.18/2.15  fof(f49198,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49197,f32850])).
% 14.18/2.15  fof(f49197,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49196,f32694])).
% 14.18/2.15  fof(f32694,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f32547,f6167])).
% 14.18/2.15  fof(f32547,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f1640,f120])).
% 14.18/2.15  fof(f49196,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f46930,f32703])).
% 14.18/2.15  fof(f32703,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f32537,f5724])).
% 14.18/2.15  fof(f32537,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f1640,f120])).
% 14.18/2.15  fof(f46930,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f199,f1640,f134,f82])).
% 14.18/2.15  fof(f49326,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49325,f27587])).
% 14.18/2.15  fof(f27587,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f27387,f27586])).
% 14.18/2.15  fof(f27586,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f27207,f5996])).
% 14.18/2.15  fof(f5996,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f5995,f3149])).
% 14.18/2.15  fof(f5995,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5994,f5950])).
% 14.18/2.15  fof(f5950,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5949,f3149])).
% 14.18/2.15  fof(f5949,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5948,f3816])).
% 14.18/2.15  fof(f5948,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5425,f3385])).
% 14.18/2.15  fof(f5425,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f199,f133,f93])).
% 14.18/2.15  fof(f5994,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5409,f2784])).
% 14.18/2.15  fof(f5409,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f202,f133,f93])).
% 14.18/2.15  fof(f27207,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f199,f1490,f110])).
% 14.18/2.15  fof(f27387,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f1490,f122])).
% 14.18/2.15  fof(f49325,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49324,f47338])).
% 14.18/2.15  fof(f47338,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47337,f1949])).
% 14.18/2.15  fof(f47337,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47336,f38687])).
% 14.18/2.15  fof(f47336,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f47335,f8180])).
% 14.18/2.15  fof(f47335,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f47334,f4460])).
% 14.18/2.15  fof(f4460,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f4120,f3798])).
% 14.18/2.15  fof(f3798,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f3772,f3792])).
% 14.18/2.15  fof(f3792,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f2992,f3789])).
% 14.18/2.15  fof(f3789,plain,(
% 14.18/2.15    sK9(sK0) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f2991,f3788])).
% 14.18/2.15  fof(f2991,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2846,f2003])).
% 14.18/2.15  fof(f2003,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f134,f119])).
% 14.18/2.15  fof(f2846,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f134,f120])).
% 14.18/2.15  fof(f2992,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f1406,f2991])).
% 14.18/2.15  fof(f1406,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f202,f110])).
% 14.18/2.15  fof(f3772,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f134,f122])).
% 14.18/2.15  fof(f4120,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f134,f123])).
% 14.18/2.15  fof(f47334,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f47333,f27613])).
% 14.18/2.15  fof(f27613,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f27414,f27608])).
% 14.18/2.15  fof(f27608,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f27440,f27607])).
% 14.18/2.15  fof(f27607,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f27198,f5756])).
% 14.18/2.15  fof(f5756,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f5604,f5749])).
% 14.18/2.15  fof(f5749,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5748,f2849])).
% 14.18/2.15  fof(f5748,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5747,f3788])).
% 14.18/2.15  fof(f5747,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5746,f5604])).
% 14.18/2.15  fof(f5746,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5492,f2789])).
% 14.18/2.15  fof(f2789,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f202,f120])).
% 14.18/2.15  fof(f5492,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f133,f202,f134,f93])).
% 14.18/2.15  fof(f5604,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5603,f3478])).
% 14.18/2.15  fof(f3478,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2696,f1925])).
% 14.18/2.15  fof(f1925,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f202,f119])).
% 14.18/2.15  fof(f2696,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f190,f120])).
% 14.18/2.15  fof(f5603,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5602,f2849])).
% 14.18/2.15  fof(f5602,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5524,f3149])).
% 14.18/2.15  fof(f5524,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f133,f134,f93])).
% 14.18/2.15  fof(f27198,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f1490,f110])).
% 14.18/2.15  fof(f27440,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f27369,f27414])).
% 14.18/2.15  fof(f27369,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f1490,f122])).
% 14.18/2.15  fof(f27414,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f1490,f123])).
% 14.18/2.15  fof(f47333,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47332,f1985])).
% 14.18/2.15  fof(f47332,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47135,f3789])).
% 14.18/2.15  fof(f47135,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f202,f133,f134,f82])).
% 14.18/2.15  fof(f49324,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49323,f8141])).
% 14.18/2.15  fof(f49323,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49322,f27613])).
% 14.18/2.15  fof(f49322,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49321,f27466])).
% 14.18/2.15  fof(f27466,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f27327,f5996])).
% 14.18/2.15  fof(f27327,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f1490,f120])).
% 14.18/2.15  fof(f49321,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f46913,f27474])).
% 14.18/2.15  fof(f27474,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f27318,f5756])).
% 14.18/2.15  fof(f27318,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f1490,f120])).
% 14.18/2.15  fof(f46913,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f199,f1490,f134,f82])).
% 14.18/2.15  fof(f48143,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f48142,f38703])).
% 14.18/2.15  fof(f38703,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f38458,f38689])).
% 14.18/2.15  fof(f38689,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f38475,f8144])).
% 14.18/2.15  fof(f8144,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3899,f8141])).
% 14.18/2.15  fof(f3899,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f1183,f3704])).
% 14.18/2.15  fof(f3704,plain,(
% 14.18/2.15    k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f199,f122])).
% 14.18/2.15  fof(f1183,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f199,f114])).
% 14.18/2.15  fof(f38475,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f1676,f120])).
% 14.18/2.15  fof(f38458,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f1676,f119])).
% 14.18/2.15  fof(f48142,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f48141,f27592])).
% 14.18/2.15  fof(f27592,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f27417,f27587])).
% 14.18/2.15  fof(f27417,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f1490,f123])).
% 14.18/2.15  fof(f48141,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f48140,f8145])).
% 14.18/2.15  fof(f48140,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f48139,f47339])).
% 14.18/2.15  fof(f47339,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f27423,f47338])).
% 14.18/2.15  fof(f27423,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f1490,f123])).
% 14.18/2.15  fof(f48139,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f48138,f27480])).
% 14.18/2.15  fof(f27480,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f27312,f6300])).
% 14.18/2.15  fof(f6300,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f6299,f3149])).
% 14.18/2.15  fof(f6299,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f6298,f3819])).
% 14.18/2.15  fof(f3819,plain,(
% 14.18/2.15    sK8(sK0) = k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f2759,f3817])).
% 14.18/2.15  fof(f2759,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f199,f120])).
% 14.18/2.15  fof(f6298,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5281,f3149])).
% 14.18/2.15  fof(f5281,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f133,f199,f93])).
% 14.18/2.15  fof(f27312,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f1490,f120])).
% 14.18/2.15  fof(f48138,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f48137,f2001])).
% 14.18/2.15  fof(f48137,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f47057,f27460])).
% 14.18/2.15  fof(f27460,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f27333,f5987])).
% 14.18/2.15  fof(f5987,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f5986,f3013])).
% 14.18/2.15  fof(f5986,plain,(
% 14.18/2.15    k1_lattices(sK0,sK9(sK0),sK8(sK0)) = k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f5985,f3149])).
% 14.18/2.15  fof(f5985,plain,(
% 14.18/2.15    k1_lattices(sK0,sK9(sK0),sK8(sK0)) = k1_lattices(sK0,sK9(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5412,f3791])).
% 14.18/2.15  fof(f3791,plain,(
% 14.18/2.15    sK9(sK0) = k1_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f2790,f3789])).
% 14.18/2.15  fof(f2790,plain,(
% 14.18/2.15    k1_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f202,f120])).
% 14.18/2.15  fof(f5412,plain,(
% 14.18/2.15    k1_lattices(sK0,sK9(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f134,f202,f133,f93])).
% 14.18/2.15  fof(f27333,plain,(
% 14.18/2.15    k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f1490,f120])).
% 14.18/2.15  fof(f47057,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f1490,f199,f134,f82])).
% 14.18/2.15  fof(f50750,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f50749,f49329])).
% 14.18/2.15  fof(f49329,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f27410,f49327])).
% 14.18/2.15  fof(f27410,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f1213,f1490,f123])).
% 14.18/2.15  fof(f50749,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f50748,f22929])).
% 14.18/2.15  fof(f22929,plain,(
% 14.18/2.15    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f22767,f6674])).
% 14.18/2.15  fof(f6674,plain,(
% 14.18/2.15    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f6673,f2995])).
% 14.18/2.15  fof(f6673,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f6672,f3791])).
% 14.18/2.15  fof(f6672,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5130,f2995])).
% 14.18/2.15  fof(f5130,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f134,f202,f93])).
% 14.18/2.15  fof(f22767,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f1213,f120])).
% 14.18/2.15  fof(f50748,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f50747,f1985])).
% 14.18/2.15  fof(f50747,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f46784,f22909])).
% 14.18/2.15  fof(f22909,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f22788,f5694])).
% 14.18/2.15  fof(f5694,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f5693,f2849])).
% 14.18/2.15  fof(f5693,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f5692,f2995])).
% 14.18/2.15  fof(f5692,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5510,f3819])).
% 14.18/2.15  fof(f5510,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f133,f199,f134,f93])).
% 14.18/2.15  fof(f22788,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f1213,f120])).
% 14.18/2.15  fof(f46784,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f1213,f202,f133,f82])).
% 14.18/2.15  fof(f50737,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f50736,f38701])).
% 14.18/2.15  fof(f50736,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f50735,f32836])).
% 14.18/2.15  fof(f32836,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f32641,f32831])).
% 14.18/2.15  fof(f32831,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f32609,f32830])).
% 14.18/2.15  fof(f32830,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f32417,f6192])).
% 14.18/2.15  fof(f6192,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f6191,f3302])).
% 14.18/2.15  fof(f6191,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f6190,f4394])).
% 14.18/2.15  fof(f6190,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f6189,f6171])).
% 14.18/2.15  fof(f6171,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f6170,f3302])).
% 14.18/2.15  fof(f6170,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5335,f2801])).
% 14.18/2.15  fof(f5335,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f202,f203,f132,f93])).
% 14.18/2.15  fof(f6189,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f5327,f3347])).
% 14.18/2.15  fof(f5327,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f202,f132,f93])).
% 14.18/2.15  fof(f32417,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f202,f1640,f110])).
% 14.18/2.15  fof(f32609,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f1640,f122])).
% 14.18/2.15  fof(f32641,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f1640,f123])).
% 14.18/2.15  fof(f50735,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f50734,f8180])).
% 14.18/2.15  fof(f50734,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f50733,f50137])).
% 14.18/2.15  fof(f50137,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f32648,f50136])).
% 14.18/2.15  fof(f50136,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f50135,f38689])).
% 14.18/2.15  fof(f50135,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f50134,f4097])).
% 14.18/2.15  fof(f50134,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f50133,f4629])).
% 14.18/2.15  fof(f4629,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f4109,f4290])).
% 14.18/2.15  fof(f4290,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f3761,f4287])).
% 14.18/2.15  fof(f4287,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f3148,f4284])).
% 14.18/2.15  fof(f4284,plain,(
% 14.18/2.15    sK8(sK0) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3147,f4235])).
% 14.18/2.15  fof(f3147,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2832,f1986])).
% 14.18/2.15  fof(f1986,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f133,f119])).
% 14.18/2.15  fof(f2832,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f133,f120])).
% 14.18/2.15  fof(f3148,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f1551,f3147])).
% 14.18/2.15  fof(f1551,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f203,f110])).
% 14.18/2.15  fof(f3761,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f133,f122])).
% 14.18/2.15  fof(f4109,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f203,f133,f123])).
% 14.18/2.15  fof(f50133,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f50132,f32863])).
% 14.18/2.15  fof(f32863,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f32638,f32858])).
% 14.18/2.15  fof(f50132,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f50131,f1968])).
% 14.18/2.15  fof(f50131,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f46830,f4284])).
% 14.18/2.15  fof(f46830,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f203,f132,f133,f82])).
% 14.18/2.15  fof(f32648,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f1640,f123])).
% 14.18/2.15  fof(f50733,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f50732,f32711])).
% 14.18/2.15  fof(f32711,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f32529,f6724])).
% 14.18/2.15  fof(f6724,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f6723,f3302])).
% 14.18/2.15  fof(f6723,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f6722,f4447])).
% 14.18/2.15  fof(f4447,plain,(
% 14.18/2.15    sK7(sK0) = k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f2788,f4445])).
% 14.18/2.15  fof(f2788,plain,(
% 14.18/2.15    k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f202,f120])).
% 14.18/2.15  fof(f6722,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5111,f3302])).
% 14.18/2.15  fof(f5111,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f203,f132,f202,f93])).
% 14.18/2.15  fof(f32529,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f1640,f120])).
% 14.18/2.15  fof(f50732,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f50731,f1985])).
% 14.18/2.15  fof(f50731,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f46786,f32689])).
% 14.18/2.15  fof(f32689,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f32552,f6161])).
% 14.18/2.15  fof(f6161,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f6160,f3175])).
% 14.18/2.15  fof(f6160,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),sK7(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f6159,f3302])).
% 14.18/2.15  fof(f6159,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),sK7(sK0)) = k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5339,f4286])).
% 14.18/2.15  fof(f4286,plain,(
% 14.18/2.15    sK8(sK0) = k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f2804,f4284])).
% 14.18/2.15  fof(f2804,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f203,f120])).
% 14.18/2.15  fof(f5339,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f133,f203,f132,f93])).
% 14.18/2.15  fof(f32552,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f1640,f120])).
% 14.18/2.15  fof(f46786,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f1640,f202,f133,f82])).
% 14.18/2.15  fof(f53824,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f53823,f51347])).
% 14.18/2.15  fof(f51347,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51346,f18967])).
% 14.18/2.15  fof(f18967,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f18966,f10809])).
% 14.18/2.15  fof(f10809,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f10808,f5755])).
% 14.18/2.15  fof(f5755,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3479,f5749])).
% 14.18/2.15  fof(f3479,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f1397,f3478])).
% 14.18/2.15  fof(f1397,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f190,f202,f110])).
% 14.18/2.15  fof(f10808,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f10807,f3654])).
% 14.18/2.15  fof(f3654,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f190,f122])).
% 14.18/2.15  fof(f10807,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f10406,f8542])).
% 14.18/2.15  fof(f8542,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f8541,f5927])).
% 14.18/2.15  fof(f5927,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3719,f5923])).
% 14.18/2.15  fof(f5923,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f4710,f5921])).
% 14.18/2.15  fof(f5921,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3574,f5916])).
% 14.18/2.15  fof(f5916,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3573,f5915])).
% 14.18/2.15  fof(f3573,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2651,f1921])).
% 14.18/2.15  fof(f1921,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f202,f119])).
% 14.18/2.15  fof(f2651,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f186,f120])).
% 14.18/2.15  fof(f3574,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f1393,f3573])).
% 14.18/2.15  fof(f1393,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f186,f202,f110])).
% 14.18/2.15  fof(f4710,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3664,f4067])).
% 14.18/2.15  fof(f4067,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f202,f123])).
% 14.18/2.15  fof(f3664,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f202,f186,f122])).
% 14.18/2.15  fof(f3719,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f202,f122])).
% 14.18/2.15  fof(f8541,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f8540,f4389])).
% 14.18/2.15  fof(f8540,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,sK9(sK0),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f7944,f4475])).
% 14.18/2.15  fof(f7944,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,sK9(sK0),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),sK7(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f124,f129,f186,f134,f132,f98])).
% 14.18/2.15  fof(f10406,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f310,f98])).
% 14.18/2.15  fof(f18966,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f18923,f18949])).
% 14.18/2.15  fof(f18949,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f310,f642,f123])).
% 14.18/2.15  fof(f18923,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f310,f642,f122])).
% 14.18/2.15  fof(f51346,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51345,f10602])).
% 14.18/2.15  fof(f10602,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f10595,f10601])).
% 14.18/2.15  fof(f10601,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f10575,f8283])).
% 14.18/2.15  fof(f8283,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f8282,f3775])).
% 14.18/2.15  fof(f8282,plain,(
% 14.18/2.15    k2_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f8281,f4475])).
% 14.18/2.15  fof(f8281,plain,(
% 14.18/2.15    k2_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f8057,f3176])).
% 14.18/2.15  fof(f3176,plain,(
% 14.18/2.15    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f417,f3175])).
% 14.18/2.15  fof(f417,plain,(
% 14.18/2.15    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k1_lattices(sK0,sK8(sK0),sK7(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f132,f110])).
% 14.18/2.15  fof(f8057,plain,(
% 14.18/2.15    k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f124,f129,f133,f186,f134,f98])).
% 14.18/2.15  fof(f10575,plain,(
% 14.18/2.15    k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f310,f122])).
% 14.18/2.15  fof(f10595,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f310,f123])).
% 14.18/2.15  fof(f51345,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51344,f18959])).
% 14.18/2.15  fof(f18959,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f18927,f8673])).
% 14.18/2.15  fof(f8673,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f8672,f4568])).
% 14.18/2.15  fof(f8672,plain,(
% 14.18/2.15    k2_lattices(sK0,sK8(sK0),sK7(sK0)) = k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f8671,f4677])).
% 14.18/2.15  fof(f8671,plain,(
% 14.18/2.15    k2_lattices(sK0,sK8(sK0),sK7(sK0)) = k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f7886,f2983])).
% 14.18/2.15  fof(f2983,plain,(
% 14.18/2.15    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f433,f2849])).
% 14.18/2.15  fof(f433,plain,(
% 14.18/2.15    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f134,f110])).
% 14.18/2.15  fof(f7886,plain,(
% 14.18/2.15    k2_lattices(sK0,sK8(sK0),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f124,f129,f133,f190,f132,f98])).
% 14.18/2.15  fof(f18927,plain,(
% 14.18/2.15    k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f642,f122])).
% 14.18/2.15  fof(f51344,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51343,f51111])).
% 14.18/2.15  fof(f51111,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f51110,f1929])).
% 14.18/2.15  fof(f51110,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f51109,f18968])).
% 14.18/2.15  fof(f18968,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f18949,f18967])).
% 14.18/2.15  fof(f51109,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51108,f18960])).
% 14.18/2.15  fof(f18960,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f18953,f18959])).
% 14.18/2.15  fof(f18953,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f642,f123])).
% 14.18/2.15  fof(f51108,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51107,f10601])).
% 14.18/2.15  fof(f51107,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f51106,f18845])).
% 14.18/2.15  fof(f18845,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f310,f642,f119])).
% 14.18/2.15  fof(f51106,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f51105,f18849])).
% 14.18/2.15  fof(f18849,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f642,f119])).
% 14.18/2.15  fof(f51105,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f46739,f50295])).
% 14.18/2.15  fof(f50295,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f49909,f50294])).
% 14.18/2.15  fof(f50294,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f50293,f18849])).
% 14.18/2.15  fof(f50293,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f50292,f19060])).
% 14.18/2.15  fof(f19060,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f18844,f19057])).
% 14.18/2.15  fof(f19057,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f18870,f19056])).
% 14.18/2.15  fof(f19056,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f18797,f8673])).
% 14.18/2.15  fof(f18797,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f642,f114])).
% 14.18/2.15  fof(f18870,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f642,f120])).
% 14.18/2.15  fof(f18844,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f642,f119])).
% 14.18/2.15  fof(f50292,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f50291,f4090])).
% 14.18/2.15  fof(f50291,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f50290,f3951])).
% 14.18/2.15  fof(f3951,plain,(
% 14.18/2.15    sK8(sK0) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f3655,f2983])).
% 14.18/2.15  fof(f3655,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f190,f122])).
% 14.18/2.15  fof(f50290,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f50289,f15876])).
% 14.18/2.15  fof(f15876,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f15855,f15875])).
% 14.18/2.15  fof(f15875,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f15831,f5571])).
% 14.18/2.15  fof(f5571,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f3010,f5567])).
% 14.18/2.15  fof(f5567,plain,(
% 14.18/2.15    k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3009,f5566])).
% 14.18/2.15  fof(f5566,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5565,f2698])).
% 14.18/2.15  fof(f2698,plain,(
% 14.18/2.15    k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f190,f120])).
% 14.18/2.15  fof(f5565,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5564,f2849])).
% 14.18/2.15  fof(f5564,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5527,f2833])).
% 14.18/2.15  fof(f5527,plain,(
% 14.18/2.15    k1_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f132,f133,f134,f93])).
% 14.18/2.15  fof(f3009,plain,(
% 14.18/2.15    k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f2837,f1993])).
% 14.18/2.15  fof(f1993,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f134,f119])).
% 14.18/2.15  fof(f2837,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f134,f120])).
% 14.18/2.15  fof(f3010,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f430,f3009])).
% 14.18/2.15  fof(f430,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f186,f134,f110])).
% 14.18/2.15  fof(f15831,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f620,f122])).
% 14.18/2.15  fof(f620,plain,(
% 14.18/2.15    m1_subset_1(k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),u1_struct_0(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f190,f118])).
% 14.18/2.15  fof(f15855,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f620,f123])).
% 14.18/2.15  fof(f50289,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f50288,f1961])).
% 14.18/2.15  fof(f1961,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f132,f119])).
% 14.18/2.15  fof(f50288,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f46823,f3470])).
% 14.18/2.15  fof(f3470,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2699,f2984])).
% 14.18/2.15  fof(f2984,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f917,f2983])).
% 14.18/2.15  fof(f917,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f190,f114])).
% 14.18/2.15  fof(f2699,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f190,f120])).
% 14.18/2.15  fof(f46823,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f190,f132,f133,f82])).
% 14.18/2.15  fof(f49909,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f4006,f49908])).
% 14.18/2.15  fof(f49908,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49907,f10515])).
% 14.18/2.15  fof(f10515,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f310,f119])).
% 14.18/2.15  fof(f49907,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f49906,f10677])).
% 14.18/2.15  fof(f10677,plain,(
% 14.18/2.15    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f10511,f10674])).
% 14.18/2.15  fof(f10674,plain,(
% 14.18/2.15    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f10531,f10673])).
% 14.18/2.15  fof(f10673,plain,(
% 14.18/2.15    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f10475,f8283])).
% 14.18/2.15  fof(f10475,plain,(
% 14.18/2.15    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f310,f114])).
% 14.18/2.15  fof(f10531,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f310,f120])).
% 14.18/2.15  fof(f10511,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f310,f119])).
% 14.18/2.15  fof(f49906,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f49905,f4115])).
% 14.18/2.15  fof(f49905,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f49904,f4123])).
% 14.18/2.15  fof(f49904,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f49903,f3936])).
% 14.18/2.15  fof(f3936,plain,(
% 14.18/2.15    sK8(sK0) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f3667,f3176])).
% 14.18/2.15  fof(f3667,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f186,f122])).
% 14.18/2.15  fof(f49903,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f49902,f15878])).
% 14.18/2.15  fof(f15878,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f15854,f15877])).
% 14.18/2.15  fof(f15877,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f15830,f3317])).
% 14.18/2.15  fof(f3317,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f587,f3316])).
% 14.18/2.15  fof(f3316,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2810,f1961])).
% 14.18/2.15  fof(f2810,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f132,f120])).
% 14.18/2.15  fof(f587,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k1_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f190,f110])).
% 14.18/2.15  fof(f15830,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f620,f122])).
% 14.18/2.15  fof(f15854,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f620,f123])).
% 14.18/2.15  fof(f49902,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f49901,f5569])).
% 14.18/2.15  fof(f5569,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f1993,f5567])).
% 14.18/2.15  fof(f49901,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f49900,f2006])).
% 14.18/2.15  fof(f49900,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f46855,f3561])).
% 14.18/2.15  fof(f3561,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2654,f3177])).
% 14.18/2.15  fof(f3177,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f865,f3176])).
% 14.18/2.15  fof(f865,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f133,f186,f114])).
% 14.18/2.15  fof(f2654,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f186,f120])).
% 14.18/2.15  fof(f46855,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f186,f134,f133,f82])).
% 14.18/2.15  fof(f46739,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f310,f642,f133,f82])).
% 14.18/2.15  fof(f51343,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f46707,f50297])).
% 14.18/2.15  fof(f50297,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f10515,f50295])).
% 14.18/2.15  fof(f46707,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f642,f310,f133,f82])).
% 14.18/2.15  fof(f53823,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f53822,f1949])).
% 14.18/2.15  fof(f53822,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f53821,f10601])).
% 14.18/2.15  fof(f53821,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f53820,f10604])).
% 14.18/2.15  fof(f10604,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f10594,f10603])).
% 14.18/2.15  fof(f10603,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f10574,f8286])).
% 14.18/2.15  fof(f10574,plain,(
% 14.18/2.15    k2_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f310,f122])).
% 14.18/2.15  fof(f10594,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f310,f123])).
% 14.18/2.15  fof(f53820,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f53819,f52841])).
% 14.18/2.15  fof(f52841,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f52840,f48480])).
% 14.18/2.15  fof(f48480,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f48479,f18964])).
% 14.18/2.15  fof(f18964,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f18963,f13216])).
% 14.18/2.15  fof(f13216,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f13215,f5577])).
% 14.18/2.15  fof(f5577,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3483,f5576])).
% 14.18/2.15  fof(f5576,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3482,f5575])).
% 14.18/2.15  fof(f3482,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2694,f1889])).
% 14.18/2.15  fof(f1889,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f199,f119])).
% 14.18/2.15  fof(f2694,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f190,f120])).
% 14.18/2.15  fof(f3483,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f1131,f3482])).
% 14.18/2.15  fof(f1131,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f190,f199,f110])).
% 14.18/2.15  fof(f13215,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f13214,f3654])).
% 14.18/2.15  fof(f13214,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f12773,f8570])).
% 14.18/2.15  fof(f8570,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f8569,f5655])).
% 14.18/2.15  fof(f5655,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3693,f5651])).
% 14.18/2.15  fof(f5651,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f4743,f5646])).
% 14.18/2.15  fof(f5646,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3515,f5645])).
% 14.18/2.15  fof(f5645,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3514,f5644])).
% 14.18/2.15  fof(f3514,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2679,f1888])).
% 14.18/2.15  fof(f1888,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f199,f119])).
% 14.18/2.15  fof(f2679,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f199,f189,f120])).
% 14.18/2.15  fof(f3515,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f1130,f3514])).
% 14.18/2.15  fof(f1130,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f189,f199,f110])).
% 14.18/2.15  fof(f4743,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f3638,f4041])).
% 14.18/2.15  fof(f4041,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f199,f123])).
% 14.18/2.15  fof(f3638,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f199,f189,f122])).
% 14.18/2.15  fof(f3693,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f199,f122])).
% 14.18/2.15  fof(f8569,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f8568,f4568])).
% 14.18/2.15  fof(f8568,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,sK8(sK0),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f7933,f4654])).
% 14.18/2.15  fof(f4654,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f3753,f4101])).
% 14.18/2.15  fof(f4101,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f133,f123])).
% 14.18/2.15  fof(f3753,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f133,f122])).
% 14.18/2.15  fof(f7933,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,sK8(sK0),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),sK7(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f124,f129,f189,f133,f132,f98])).
% 14.18/2.15  fof(f12773,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f569,f98])).
% 14.18/2.15  fof(f569,plain,(
% 14.18/2.15    m1_subset_1(k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),u1_struct_0(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f189,f121])).
% 14.18/2.15  fof(f18963,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f18924,f18950])).
% 14.18/2.15  fof(f18950,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f569,f642,f123])).
% 14.18/2.15  fof(f18924,plain,(
% 14.18/2.15    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f569,f642,f122])).
% 14.18/2.15  fof(f48479,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f48478,f12986])).
% 14.18/2.15  fof(f12986,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f12982,f12985])).
% 14.18/2.15  fof(f12985,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f12960,f8499])).
% 14.18/2.15  fof(f8499,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f8498,f4232])).
% 14.18/2.15  fof(f4232,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),sK9(sK0)) = k2_lattices(sK0,sK9(sK0),sK8(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f3764,f4123])).
% 14.18/2.15  fof(f8498,plain,(
% 14.18/2.15    k2_lattices(sK0,sK9(sK0),sK8(sK0)) = k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f8497,f4654])).
% 14.18/2.15  fof(f8497,plain,(
% 14.18/2.15    k2_lattices(sK0,sK9(sK0),sK8(sK0)) = k2_lattices(sK0,sK9(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f7959,f3172])).
% 14.18/2.15  fof(f3172,plain,(
% 14.18/2.15    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f418,f3171])).
% 14.18/2.15  fof(f418,plain,(
% 14.18/2.15    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k1_lattices(sK0,sK9(sK0),sK7(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f132,f110])).
% 14.18/2.15  fof(f7959,plain,(
% 14.18/2.15    k2_lattices(sK0,sK9(sK0),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k2_lattices(sK0,k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f124,f129,f134,f189,f133,f98])).
% 14.18/2.15  fof(f12960,plain,(
% 14.18/2.15    k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f569,f122])).
% 14.18/2.15  fof(f12982,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f569,f123])).
% 14.18/2.15  fof(f48478,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f48477,f18957])).
% 14.18/2.15  fof(f48477,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f48476,f48365])).
% 14.18/2.15  fof(f48365,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f48364,f18965])).
% 14.18/2.15  fof(f18965,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f18950,f18964])).
% 14.18/2.15  fof(f48364,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f48363,f18958])).
% 14.18/2.15  fof(f18958,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f18954,f18957])).
% 14.18/2.15  fof(f18954,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f642,f123])).
% 14.18/2.15  fof(f48363,plain,(
% 14.18/2.15    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f48362,f12985])).
% 14.18/2.15  fof(f48362,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f48361,f18846])).
% 14.18/2.15  fof(f18846,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f569,f642,f119])).
% 14.18/2.15  fof(f48361,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f48360,f18850])).
% 14.18/2.15  fof(f18850,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f642,f119])).
% 14.18/2.15  fof(f48360,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f47029,f47625])).
% 14.18/2.15  fof(f47625,plain,(
% 14.18/2.15    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f47431,f47624])).
% 14.18/2.15  fof(f47624,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f47623,f18850])).
% 14.18/2.15  fof(f47623,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47622,f19055])).
% 14.18/2.15  fof(f19055,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f18842,f19052])).
% 14.18/2.15  fof(f19052,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f18868,f19051])).
% 14.18/2.15  fof(f19051,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f18798,f8670])).
% 14.18/2.15  fof(f18798,plain,(
% 14.18/2.15    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f642,f114])).
% 14.18/2.15  fof(f18868,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f642,f120])).
% 14.18/2.15  fof(f18842,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f202,f642,f119])).
% 14.18/2.15  fof(f47622,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47621,f4090])).
% 14.18/2.15  fof(f47621,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47620,f3949])).
% 14.18/2.15  fof(f3949,plain,(
% 14.18/2.15    sK9(sK0) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f3656,f3014])).
% 14.18/2.15  fof(f3656,plain,(
% 14.18/2.15    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f190,f122])).
% 14.18/2.15  fof(f47620,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f47619,f15880])).
% 14.18/2.15  fof(f15880,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f15853,f15879])).
% 14.18/2.15  fof(f15879,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f15829,f5631])).
% 14.18/2.15  fof(f5631,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f3164,f5626])).
% 14.18/2.15  fof(f5626,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5625,f5566])).
% 14.18/2.15  fof(f5625,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5624,f2684])).
% 14.18/2.15  fof(f2684,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f133,f189,f120])).
% 14.18/2.15  fof(f5624,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5623,f2848])).
% 14.18/2.15  fof(f5623,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f5519,f3175])).
% 14.18/2.15  fof(f5519,plain,(
% 14.18/2.15    k1_lattices(sK0,sK8(sK0),k1_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,sK8(sK0),sK7(sK0)),sK9(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f125,f127,f133,f132,f134,f93])).
% 14.18/2.15  fof(f3164,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f519,f3163])).
% 14.18/2.15  fof(f3163,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2824,f1978])).
% 14.18/2.15  fof(f1978,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f133,f119])).
% 14.18/2.15  fof(f2824,plain,(
% 14.18/2.15    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f133,f120])).
% 14.18/2.15  fof(f519,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f189,f110])).
% 14.18/2.15  fof(f15829,plain,(
% 14.18/2.15    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f620,f122])).
% 14.18/2.15  fof(f15853,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f620,f123])).
% 14.18/2.15  fof(f47619,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f47618,f1961])).
% 14.18/2.15  fof(f47618,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f47112,f3465])).
% 14.18/2.15  fof(f3465,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2700,f3015])).
% 14.18/2.15  fof(f3015,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f918,f3014])).
% 14.18/2.15  fof(f918,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f190,f114])).
% 14.18/2.15  fof(f2700,plain,(
% 14.18/2.15    k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f190,f120])).
% 14.18/2.15  fof(f47112,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f190,f132,f134,f82])).
% 14.18/2.15  fof(f47431,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f3993,f47430])).
% 14.18/2.15  fof(f47430,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f47429,f12894])).
% 14.18/2.15  fof(f12894,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f569,f119])).
% 14.18/2.15  fof(f47429,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47428,f13068])).
% 14.18/2.15  fof(f13068,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f12888,f13065])).
% 14.18/2.15  fof(f13065,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f12910,f13064])).
% 14.18/2.15  fof(f13064,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f12850,f8499])).
% 14.18/2.15  fof(f12850,plain,(
% 14.18/2.15    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f569,f114])).
% 14.18/2.15  fof(f12910,plain,(
% 14.18/2.15    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f569,f120])).
% 14.18/2.15  fof(f12888,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f203,f569,f119])).
% 14.18/2.15  fof(f47428,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47427,f4101])).
% 14.18/2.15  fof(f47427,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f47426,f3963])).
% 14.18/2.15  fof(f3963,plain,(
% 14.18/2.15    sK9(sK0) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f3644,f3172])).
% 14.18/2.15  fof(f3644,plain,(
% 14.18/2.15    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f189,f122])).
% 14.18/2.15  fof(f47426,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(forward_demodulation,[],[f47425,f15878])).
% 14.18/2.15  fof(f47425,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f47424,f5628])).
% 14.18/2.15  fof(f5628,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f1978,f5626])).
% 14.18/2.15  fof(f47424,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f47128,f3497])).
% 14.18/2.15  fof(f3497,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f2685,f3173])).
% 14.18/2.15  fof(f3173,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f905,f3172])).
% 14.18/2.15  fof(f905,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f81,f130,f134,f189,f114])).
% 14.18/2.15  fof(f2685,plain,(
% 14.18/2.15    k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f189,f120])).
% 14.18/2.15  fof(f47128,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f189,f133,f134,f82])).
% 14.18/2.15  fof(f3993,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f190,f123])).
% 14.18/2.15  fof(f47029,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f569,f642,f134,f82])).
% 14.18/2.15  fof(f48476,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f47013,f47627])).
% 14.18/2.15  fof(f47627,plain,(
% 14.18/2.15    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f12894,f47625])).
% 14.18/2.15  fof(f47013,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f642,f569,f134,f82])).
% 14.18/2.15  fof(f52840,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f52839,f1947])).
% 14.18/2.15  fof(f52839,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f52838,f10602])).
% 14.18/2.15  fof(f52838,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f52837,f4110])).
% 14.18/2.15  fof(f52837,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f52836,f10603])).
% 14.18/2.15  fof(f52836,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f52835,f51825])).
% 14.18/2.15  fof(f51825,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(backward_demodulation,[],[f51133,f51824])).
% 14.18/2.15  fof(f51824,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f51823,f51507])).
% 14.18/2.15  fof(f51507,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51506,f50355])).
% 14.18/2.15  fof(f50355,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.15    inference(backward_demodulation,[],[f49908,f50295])).
% 14.18/2.15  fof(f51506,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51505,f18849])).
% 14.18/2.15  fof(f51505,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51504,f4649])).
% 14.18/2.15  fof(f4649,plain,(
% 14.18/2.15    sK8(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f4102,f3951])).
% 14.18/2.15  fof(f4102,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f133,f123])).
% 14.18/2.15  fof(f51504,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51503,f4110])).
% 14.18/2.15  fof(f51503,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51502,f15878])).
% 14.18/2.15  fof(f51502,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51501,f3473])).
% 14.18/2.15  fof(f3473,plain,(
% 14.18/2.15    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),
% 14.18/2.15    inference(backward_demodulation,[],[f1979,f3470])).
% 14.18/2.15  fof(f1979,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f133,f119])).
% 14.18/2.15  fof(f51501,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f46695,f1987])).
% 14.18/2.15  fof(f46695,plain,(
% 14.18/2.15    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK7(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f132,f190,f133,f82])).
% 14.18/2.15  fof(f51823,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51822,f18849])).
% 14.18/2.15  fof(f51822,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51821,f18978])).
% 14.18/2.15  fof(f51821,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51820,f4645])).
% 14.18/2.15  fof(f4645,plain,(
% 14.18/2.15    sK8(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),
% 14.18/2.15    inference(forward_demodulation,[],[f4103,f3936])).
% 14.18/2.15  fof(f4103,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f133,f123])).
% 14.18/2.15  fof(f51820,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(forward_demodulation,[],[f51819,f18959])).
% 14.18/2.15  fof(f51819,plain,(
% 14.18/2.15    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.15    inference(forward_demodulation,[],[f51818,f325])).
% 14.18/2.15  fof(f325,plain,(
% 14.18/2.15    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.15    inference(unit_resulting_resolution,[],[f79,f128,f130,f131,f81,f186,f104])).
% 14.18/2.15  fof(f104,plain,(
% 14.18/2.15    ( ! [X0,X1] : (~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattices(X0,X1,X1) = X1 | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 14.18/2.15    inference(cnf_transformation,[],[f30])).
% 14.18/2.16  fof(f30,plain,(
% 14.18/2.16    ! [X0] : (! [X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 14.18/2.16    inference(flattening,[],[f29])).
% 14.18/2.16  fof(f29,plain,(
% 14.18/2.16    ! [X0] : (! [X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 14.18/2.16    inference(ennf_transformation,[],[f15])).
% 14.18/2.16  fof(f15,axiom,(
% 14.18/2.16    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,X1,X1) = X1))),
% 14.18/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattices)).
% 14.18/2.16  fof(f51818,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51817,f19091])).
% 14.18/2.16  fof(f19091,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(backward_demodulation,[],[f18840,f19089])).
% 14.18/2.16  fof(f19089,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f19031,f19088])).
% 14.18/2.16  fof(f19088,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f18775,f9299])).
% 14.18/2.16  fof(f9299,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f9298,f4677])).
% 14.18/2.16  fof(f9298,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f9297,f3144])).
% 14.18/2.16  fof(f9297,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f7601,f4677])).
% 14.18/2.16  fof(f7601,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f186,f98])).
% 14.18/2.16  fof(f18775,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f130,f186,f642,f114])).
% 14.18/2.16  fof(f19031,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f18853,f18840])).
% 14.18/2.16  fof(f18853,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f642,f120])).
% 14.18/2.16  fof(f18840,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f642,f119])).
% 14.18/2.16  fof(f51817,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f46656,f3564])).
% 14.18/2.16  fof(f3564,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),
% 14.18/2.16    inference(backward_demodulation,[],[f1975,f3561])).
% 14.18/2.16  fof(f1975,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f133,f119])).
% 14.18/2.16  fof(f46656,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f642,f186,f133,f82])).
% 14.18/2.16  fof(f51133,plain,(
% 14.18/2.16    k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f51132,f18849])).
% 14.18/2.16  fof(f51132,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f51131,f19060])).
% 14.18/2.16  fof(f51131,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f51130,f18977])).
% 14.18/2.16  fof(f51130,plain,(
% 14.18/2.16    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f51129,f18960])).
% 14.18/2.16  fof(f51129,plain,(
% 14.18/2.16    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),sK8(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f51128,f3936])).
% 14.18/2.16  fof(f51128,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f51127,f19089])).
% 14.18/2.16  fof(f51127,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f51126,f18849])).
% 14.18/2.16  fof(f51126,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f46736,f3561])).
% 14.18/2.16  fof(f46736,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f186,f642,f133,f82])).
% 14.18/2.16  fof(f52835,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f52834,f50297])).
% 14.18/2.16  fof(f52834,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f52833,f1987])).
% 14.18/2.16  fof(f52833,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK7(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f46552,f50402])).
% 14.18/2.16  fof(f50402,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f50401,f4618])).
% 14.18/2.16  fof(f50401,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f50400,f4679])).
% 14.18/2.16  fof(f4679,plain,(
% 14.18/2.16    sK7(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f4089,f3966])).
% 14.18/2.16  fof(f4089,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f132,f123])).
% 14.18/2.16  fof(f50400,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f50399,f47735])).
% 14.18/2.16  fof(f47735,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f47734,f4445])).
% 14.18/2.16  fof(f47734,plain,(
% 14.18/2.16    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f47733,f4672])).
% 14.18/2.16  fof(f47733,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f47732,f3569])).
% 14.18/2.16  fof(f3569,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0))),
% 14.18/2.16    inference(backward_demodulation,[],[f1957,f3566])).
% 14.18/2.16  fof(f3566,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f2653,f3145])).
% 14.18/2.16  fof(f3145,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(backward_demodulation,[],[f864,f3144])).
% 14.18/2.16  fof(f864,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f186,f114])).
% 14.18/2.16  fof(f2653,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f186,f120])).
% 14.18/2.16  fof(f1957,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f132,f119])).
% 14.18/2.16  fof(f47732,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f47110,f5567])).
% 14.18/2.16  fof(f47110,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f186,f132,f134,f82])).
% 14.18/2.16  fof(f50399,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f50398,f4005])).
% 14.18/2.16  fof(f4005,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f186,f123])).
% 14.18/2.16  fof(f50398,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f50397,f3506])).
% 14.18/2.16  fof(f3506,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))),
% 14.18/2.16    inference(backward_demodulation,[],[f1960,f3503])).
% 14.18/2.16  fof(f3503,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f2683,f2987])).
% 14.18/2.16  fof(f2987,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(backward_demodulation,[],[f903,f2986])).
% 14.18/2.16  fof(f903,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f130,f132,f189,f114])).
% 14.18/2.16  fof(f2683,plain,(
% 14.18/2.16    k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f189,f120])).
% 14.18/2.16  fof(f1960,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f132,f119])).
% 14.18/2.16  fof(f50397,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f46822,f5626])).
% 14.18/2.16  fof(f46822,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f189,f132,f133,f82])).
% 14.18/2.16  fof(f46552,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK7(sK0))),k4_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0)),k3_lattices(sK0,sK8(sK0),sK7(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f310,f133,f132,f82])).
% 14.18/2.16  fof(f53819,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f53818,f50295])).
% 14.18/2.16  fof(f53818,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f46424,f50404])).
% 14.18/2.16  fof(f50404,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f10514,f50402])).
% 14.18/2.16  fof(f10514,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f132,f310,f119])).
% 14.18/2.16  fof(f46424,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f133,f310,f132,f82])).
% 14.18/2.16  fof(f51352,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(backward_demodulation,[],[f49766,f51347])).
% 14.18/2.16  fof(f49766,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f49765,f4123])).
% 14.18/2.16  fof(f49765,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f49764,f4110])).
% 14.18/2.16  fof(f49764,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f49763,f47624])).
% 14.18/2.16  fof(f49763,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f49762,f2006])).
% 14.18/2.16  fof(f49762,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f46865,f1987])).
% 14.18/2.16  fof(f46865,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK9(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK7(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f132,f134,f133,f82])).
% 14.18/2.16  fof(f64586,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f64585,f49668])).
% 14.18/2.16  fof(f49668,plain,(
% 14.18/2.16    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f49667,f48773])).
% 14.18/2.16  fof(f48773,plain,(
% 14.18/2.16    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f48772,f47681])).
% 14.18/2.16  fof(f47681,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f47430,f47625])).
% 14.18/2.16  fof(f48772,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f48771,f18850])).
% 14.18/2.16  fof(f48771,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f48770,f4477])).
% 14.18/2.16  fof(f4477,plain,(
% 14.18/2.16    sK9(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f4114,f3949])).
% 14.18/2.16  fof(f4114,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f134,f123])).
% 14.18/2.16  fof(f48770,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f48769,f4122])).
% 14.18/2.16  fof(f48769,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),sK7(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f48768,f15878])).
% 14.18/2.16  fof(f48768,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f48767,f3468])).
% 14.18/2.16  fof(f3468,plain,(
% 14.18/2.16    k3_lattices(sK0,sK8(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.16    inference(backward_demodulation,[],[f1997,f3465])).
% 14.18/2.16  fof(f1997,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f190,f134,f119])).
% 14.18/2.16  fof(f48767,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f46984,f2005])).
% 14.18/2.16  fof(f46984,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k4_lattices(sK0,sK9(sK0),sK7(sK0))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))),k3_lattices(sK0,sK9(sK0),sK7(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f132,f190,f134,f82])).
% 14.18/2.16  fof(f49667,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f49666,f18850])).
% 14.18/2.16  fof(f49666,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f49665,f18976])).
% 14.18/2.16  fof(f18976,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f18945,f18975])).
% 14.18/2.16  fof(f18975,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f18919,f16126])).
% 14.18/2.16  fof(f16126,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f16125,f3654])).
% 14.18/2.16  fof(f16125,plain,(
% 14.18/2.16    k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f15636,f15883])).
% 14.18/2.16  fof(f15883,plain,(
% 14.18/2.16    sK7(sK0) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f15826,f15872])).
% 14.18/2.16  fof(f15872,plain,(
% 14.18/2.16    sK7(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.16    inference(backward_demodulation,[],[f15862,f15871])).
% 14.18/2.16  fof(f15871,plain,(
% 14.18/2.16    sK7(sK0) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f15838,f3475])).
% 14.18/2.16  fof(f3475,plain,(
% 14.18/2.16    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f598,f2698])).
% 14.18/2.16  fof(f598,plain,(
% 14.18/2.16    sK7(sK0) = k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f131,f132,f190,f110])).
% 14.18/2.16  fof(f15838,plain,(
% 14.18/2.16    k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f620,f122])).
% 14.18/2.16  fof(f15862,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f620,f123])).
% 14.18/2.16  fof(f15826,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f620,f122])).
% 14.18/2.16  fof(f15636,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f620,f98])).
% 14.18/2.16  fof(f18919,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f620,f642,f122])).
% 14.18/2.16  fof(f18945,plain,(
% 14.18/2.16    k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f620,f642,f123])).
% 14.18/2.16  fof(f49665,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),sK9(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f49664,f15868])).
% 14.18/2.16  fof(f15868,plain,(
% 14.18/2.16    sK9(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(backward_demodulation,[],[f15864,f15867])).
% 14.18/2.16  fof(f15867,plain,(
% 14.18/2.16    sK9(sK0) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f15840,f5572])).
% 14.18/2.16  fof(f5572,plain,(
% 14.18/2.16    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f3560,f5567])).
% 14.18/2.16  fof(f3560,plain,(
% 14.18/2.16    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f402,f2655])).
% 14.18/2.16  fof(f2655,plain,(
% 14.18/2.16    k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f186,f120])).
% 14.18/2.16  fof(f402,plain,(
% 14.18/2.16    sK9(sK0) = k2_lattices(sK0,sK9(sK0),k1_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f186,f110])).
% 14.18/2.16  fof(f15840,plain,(
% 14.18/2.16    k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f620,f122])).
% 14.18/2.16  fof(f15864,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f134,f620,f123])).
% 14.18/2.16  fof(f49664,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f49663,f18957])).
% 14.18/2.16  fof(f49663,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f49662,f16040])).
% 14.18/2.16  fof(f16040,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f15832,f16039])).
% 14.18/2.16  fof(f16039,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f15684,f5573])).
% 14.18/2.16  fof(f5573,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(backward_demodulation,[],[f5556,f5567])).
% 14.18/2.16  fof(f5556,plain,(
% 14.18/2.16    k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f5555,f3009])).
% 14.18/2.16  fof(f5555,plain,(
% 14.18/2.16    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f5554,f137])).
% 14.18/2.16  fof(f137,plain,(
% 14.18/2.16    sK9(sK0) = k1_lattices(sK0,sK9(sK0),sK9(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f130,f131,f81,f134,f103])).
% 14.18/2.16  fof(f103,plain,(
% 14.18/2.16    ( ! [X0,X1] : (~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_lattices(X0,X1,X1) = X1 | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 14.18/2.16    inference(cnf_transformation,[],[f28])).
% 14.18/2.16  fof(f28,plain,(
% 14.18/2.16    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 14.18/2.16    inference(flattening,[],[f27])).
% 14.18/2.16  fof(f27,plain,(
% 14.18/2.16    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 14.18/2.16    inference(ennf_transformation,[],[f14])).
% 14.18/2.16  fof(f14,axiom,(
% 14.18/2.16    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 14.18/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).
% 14.18/2.16  fof(f5554,plain,(
% 14.18/2.16    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f5532,f3009])).
% 14.18/2.16  fof(f5532,plain,(
% 14.18/2.16    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,sK9(sK0),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),sK9(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f125,f127,f186,f134,f134,f93])).
% 14.18/2.16  fof(f15684,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f620,f110])).
% 14.18/2.16  fof(f15832,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f620,f620,f122])).
% 14.18/2.16  fof(f49662,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f49661,f19086])).
% 14.18/2.16  fof(f19086,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f18841,f19084])).
% 14.18/2.16  fof(f19084,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f19030,f19083])).
% 14.18/2.16  fof(f19083,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f18776,f16590])).
% 14.18/2.16  fof(f16590,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f16589,f4677])).
% 14.18/2.16  fof(f16589,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f16588,f3475])).
% 14.18/2.16  fof(f16588,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f15348,f4677])).
% 14.18/2.16  fof(f15348,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f620,f98])).
% 14.18/2.16  fof(f18776,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f130,f620,f642,f114])).
% 14.18/2.16  fof(f19030,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f18854,f18841])).
% 14.18/2.16  fof(f18854,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f620,f642,f120])).
% 14.18/2.16  fof(f18841,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f620,f642,f119])).
% 14.18/2.16  fof(f49661,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f46877,f15918])).
% 14.18/2.16  fof(f15918,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f15780,f5573])).
% 14.18/2.16  fof(f15780,plain,(
% 14.18/2.16    k1_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f620,f120])).
% 14.18/2.16  fof(f46877,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f642,f620,f134,f82])).
% 14.18/2.16  fof(f64585,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f64584,f5569])).
% 14.18/2.16  fof(f64584,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f45121,f19091])).
% 14.18/2.16  fof(f45121,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f186,f134,f642,f82])).
% 14.18/2.16  fof(f51385,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f18845,f51384])).
% 14.18/2.16  fof(f51384,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f48524,f51383])).
% 14.18/2.16  fof(f51383,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51382,f10677])).
% 14.18/2.16  fof(f51382,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51381,f10615])).
% 14.18/2.16  fof(f10615,plain,(
% 14.18/2.16    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f10567,f8330])).
% 14.18/2.16  fof(f8330,plain,(
% 14.18/2.16    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f8301,f8329])).
% 14.18/2.16  fof(f8329,plain,(
% 14.18/2.16    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f8328,f4475])).
% 14.18/2.16  fof(f8328,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f8327,f4483])).
% 14.18/2.16  fof(f4483,plain,(
% 14.18/2.16    sK9(sK0) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.16    inference(backward_demodulation,[],[f3765,f4481])).
% 14.18/2.16  fof(f4481,plain,(
% 14.18/2.16    sK9(sK0) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f4113,f3963])).
% 14.18/2.16  fof(f4113,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f134,f123])).
% 14.18/2.16  fof(f3765,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f134,f122])).
% 14.18/2.16  fof(f8327,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f8034,f3635])).
% 14.18/2.16  fof(f3635,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f189,f122])).
% 14.18/2.16  fof(f8034,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f186,f189,f134,f98])).
% 14.18/2.16  fof(f8301,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f8300,f4475])).
% 14.18/2.16  fof(f8300,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f8050,f4782])).
% 14.18/2.16  fof(f4782,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(backward_demodulation,[],[f3657,f4005])).
% 14.18/2.16  fof(f3657,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f186,f122])).
% 14.18/2.16  fof(f8050,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK9(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f189,f186,f134,f98])).
% 14.18/2.16  fof(f10567,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f310,f122])).
% 14.18/2.16  fof(f51381,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51380,f10602])).
% 14.18/2.16  fof(f51380,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51379,f51125])).
% 14.18/2.16  fof(f51125,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51124,f19060])).
% 14.18/2.16  fof(f51124,plain,(
% 14.18/2.16    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51123,f18981])).
% 14.18/2.16  fof(f18981,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f18916,f8707])).
% 14.18/2.16  fof(f8707,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f8706,f4677])).
% 14.18/2.16  fof(f8706,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f8705,f4681])).
% 14.18/2.16  fof(f4681,plain,(
% 14.18/2.16    sK7(sK0) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))),
% 14.18/2.16    inference(backward_demodulation,[],[f3741,f4679])).
% 14.18/2.16  fof(f3741,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f132,f122])).
% 14.18/2.16  fof(f8705,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f8704,f8692])).
% 14.18/2.16  fof(f8692,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f8691,f4677])).
% 14.18/2.16  fof(f8691,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f7879,f3645])).
% 14.18/2.16  fof(f3645,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f190,f122])).
% 14.18/2.16  fof(f7879,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f189,f190,f132,f98])).
% 14.18/2.16  fof(f8704,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f7871,f4790])).
% 14.18/2.16  fof(f4790,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(backward_demodulation,[],[f3634,f3993])).
% 14.18/2.16  fof(f3634,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f190,f189,f122])).
% 14.18/2.16  fof(f7871,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f189,f132,f98])).
% 14.18/2.16  fof(f18916,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f189,f642,f122])).
% 14.18/2.16  fof(f51123,plain,(
% 14.18/2.16    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51122,f18960])).
% 14.18/2.16  fof(f51122,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51121,f19095])).
% 14.18/2.16  fof(f19095,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f19034,f19094])).
% 14.18/2.16  fof(f19094,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f18773,f9701])).
% 14.18/2.16  fof(f9701,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f9700,f4677])).
% 14.18/2.16  fof(f9700,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f9699,f2986])).
% 14.18/2.16  fof(f9699,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f7439,f4677])).
% 14.18/2.16  fof(f7439,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f190,f132,f189,f98])).
% 14.18/2.16  fof(f18773,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f130,f189,f642,f114])).
% 14.18/2.16  fof(f19034,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f18851,f18838])).
% 14.18/2.16  fof(f18838,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f642,f119])).
% 14.18/2.16  fof(f18851,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f642,f120])).
% 14.18/2.16  fof(f51121,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51120,f18849])).
% 14.18/2.16  fof(f51120,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f46737,f5626])).
% 14.18/2.16  fof(f46737,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f189,f642,f133,f82])).
% 14.18/2.16  fof(f51379,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51378,f10704])).
% 14.18/2.16  fof(f10704,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f10656,f10703])).
% 14.18/2.16  fof(f10703,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f10457,f9651])).
% 14.18/2.16  fof(f9651,plain,(
% 14.18/2.16    k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f9650,f4475])).
% 14.18/2.16  fof(f9650,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f9649,f3172])).
% 14.18/2.16  fof(f9649,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f7458,f4475])).
% 14.18/2.16  fof(f7458,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f186,f134,f189,f98])).
% 14.18/2.16  fof(f10457,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK9(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f130,f189,f310,f114])).
% 14.18/2.16  fof(f10656,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f10517,f10507])).
% 14.18/2.16  fof(f10507,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f310,f119])).
% 14.18/2.16  fof(f10517,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f189,f310,f120])).
% 14.18/2.16  fof(f51378,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f51377,f50297])).
% 14.18/2.16  fof(f51377,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f46703,f5626])).
% 14.18/2.16  fof(f46703,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),k3_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f189,f310,f133,f82])).
% 14.18/2.16  fof(f48524,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f12890,f48523])).
% 14.18/2.16  fof(f48523,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48522,f13068])).
% 14.18/2.16  fof(f48522,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48521,f13000])).
% 14.18/2.16  fof(f13000,plain,(
% 14.18/2.16    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f12952,f8517])).
% 14.18/2.16  fof(f8517,plain,(
% 14.18/2.16    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f8516,f4654])).
% 14.18/2.16  fof(f8516,plain,(
% 14.18/2.16    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f8515,f8480])).
% 14.18/2.16  fof(f8480,plain,(
% 14.18/2.16    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f8479,f4654])).
% 14.18/2.16  fof(f8479,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f8478,f4647])).
% 14.18/2.16  fof(f4647,plain,(
% 14.18/2.16    sK8(sK0) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),
% 14.18/2.16    inference(backward_demodulation,[],[f3755,f4645])).
% 14.18/2.16  fof(f3755,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f133,f122])).
% 14.18/2.16  fof(f8478,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f7969,f4782])).
% 14.18/2.16  fof(f7969,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),sK8(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0))),sK8(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f189,f186,f133,f98])).
% 14.18/2.16  fof(f8515,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k2_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f7953,f3635])).
% 14.18/2.16  fof(f7953,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f186,f189,f133,f98])).
% 14.18/2.16  fof(f12952,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f186,f569,f122])).
% 14.18/2.16  fof(f48521,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48520,f12986])).
% 14.18/2.16  fof(f48520,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48519,f48395])).
% 14.18/2.16  fof(f48395,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48394,f19055])).
% 14.18/2.16  fof(f48394,plain,(
% 14.18/2.16    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48393,f18977])).
% 14.18/2.16  fof(f48393,plain,(
% 14.18/2.16    k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48392,f18958])).
% 14.18/2.16  fof(f48392,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48391,f19089])).
% 14.18/2.16  fof(f48391,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48390,f18850])).
% 14.18/2.16  fof(f48390,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f47025,f5567])).
% 14.18/2.16  fof(f47025,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f186,f642,f134,f82])).
% 14.18/2.16  fof(f48519,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48518,f13094])).
% 14.18/2.16  fof(f13094,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f13046,f13093])).
% 14.18/2.16  fof(f13093,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f12831,f9277])).
% 14.18/2.16  fof(f9277,plain,(
% 14.18/2.16    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f9276,f4654])).
% 14.18/2.16  fof(f9276,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f9275,f3176])).
% 14.18/2.16  fof(f9275,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f7609,f4654])).
% 14.18/2.16  fof(f7609,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f189,f133,f186,f98])).
% 14.18/2.16  fof(f12831,plain,(
% 14.18/2.16    k3_lattices(sK0,sK7(sK0),sK8(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f130,f186,f569,f114])).
% 14.18/2.16  fof(f13046,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f12897,f12886])).
% 14.18/2.16  fof(f12886,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f569,f119])).
% 14.18/2.16  fof(f12897,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK8(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f186,f569,f120])).
% 14.18/2.16  fof(f48518,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f48517,f47627])).
% 14.18/2.16  fof(f48517,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f47008,f5567])).
% 14.18/2.16  fof(f47008,plain,(
% 14.18/2.16    k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,k3_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))),k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f186,f569,f134,f82])).
% 14.18/2.16  fof(f12890,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK9(sK0),k3_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f310,f569,f119])).
% 14.18/2.16  fof(f19106,plain,(
% 14.18/2.16    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f18768,f19025])).
% 14.18/2.16  fof(f19025,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f18872,f18846])).
% 14.18/2.16  fof(f18872,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f569,f642,f120])).
% 14.18/2.16  fof(f18768,plain,(
% 14.18/2.16    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f131,f569,f642,f110])).
% 14.18/2.16  fof(f55433,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK9(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(backward_demodulation,[],[f55332,f55370])).
% 14.18/2.16  fof(f55332,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f50176,f55295])).
% 14.18/2.16  fof(f50176,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(backward_demodulation,[],[f33729,f50137])).
% 14.18/2.16  fof(f33729,plain,(
% 14.18/2.16    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f33728,f32588])).
% 14.18/2.16  fof(f32588,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f1490,f1640,f122])).
% 14.18/2.16  fof(f33728,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f33727,f32968])).
% 14.18/2.16  fof(f32968,plain,(
% 14.18/2.16    k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f32967,f32662])).
% 14.18/2.16  fof(f32662,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f32600,f32648])).
% 14.18/2.16  fof(f32600,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f133,f1640,f122])).
% 14.18/2.16  fof(f32967,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f32966,f3345])).
% 14.18/2.16  fof(f3345,plain,(
% 14.18/2.16    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f1422,f2789])).
% 14.18/2.16  fof(f1422,plain,(
% 14.18/2.16    sK8(sK0) = k2_lattices(sK0,sK8(sK0),k1_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f131,f133,f202,f110])).
% 14.18/2.16  fof(f32966,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f32362,f32662])).
% 14.18/2.16  fof(f32362,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f1490,f133,f1640,f98])).
% 14.18/2.16  fof(f33727,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f32058,f33279])).
% 14.18/2.16  fof(f33279,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f32655,f33277])).
% 14.18/2.16  fof(f33277,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f32597,f33276])).
% 14.18/2.16  fof(f33276,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f33275,f32662])).
% 14.18/2.16  fof(f33275,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f33274,f4654])).
% 14.18/2.16  fof(f33274,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK8(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f32230,f32844])).
% 14.18/2.16  fof(f32230,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),sK9(sK0)),sK8(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK8(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f133,f189,f1640,f98])).
% 14.18/2.16  fof(f32597,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f569,f1640,f122])).
% 14.18/2.16  fof(f32655,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f32613,f32645])).
% 14.18/2.16  fof(f32645,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f569,f1640,f123])).
% 14.18/2.16  fof(f32613,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f569,f1640,f122])).
% 14.18/2.16  fof(f32058,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))) = k2_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),k3_lattices(sK0,sK7(sK0),k4_lattices(sK0,sK8(sK0),sK9(sK0)))),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f1490,f569,f1640,f98])).
% 14.18/2.16  fof(f5733,plain,(
% 14.18/2.16    k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f5732,f2995])).
% 14.18/2.16  fof(f5732,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),sK9(sK0)) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f5731,f3780])).
% 14.18/2.16  fof(f5731,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f5499,f2799])).
% 14.18/2.16  fof(f5499,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),sK9(sK0)),sK9(sK0))) = k1_lattices(sK0,k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f125,f127,f199,f203,f134,f93])).
% 14.18/2.16  fof(f47629,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f13038,f47625])).
% 14.18/2.16  fof(f13038,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f12905,f12894])).
% 14.18/2.16  fof(f12905,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK8(sK0),k3_lattices(sK0,sK7(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f569,f120])).
% 14.18/2.16  fof(f19115,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))))),
% 14.18/2.16    inference(forward_demodulation,[],[f18759,f19021])).
% 14.18/2.16  fof(f19021,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f18863,f18850])).
% 14.18/2.16  fof(f18863,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)) = k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f126,f125,f134,f642,f120])).
% 14.18/2.16  fof(f18759,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK9(sK0)))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f81,f131,f134,f642,f110])).
% 14.18/2.16  fof(f52601,plain,(
% 14.18/2.16    k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) = k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f50220,f52539])).
% 14.18/2.16  fof(f50220,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),k4_lattices(sK0,sK7(sK0),sK9(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f23395,f50199])).
% 14.18/2.16  fof(f23395,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f22878,f23393])).
% 14.18/2.16  fof(f23393,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(backward_demodulation,[],[f22828,f23392])).
% 14.18/2.16  fof(f23392,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f23391,f22885])).
% 14.18/2.16  fof(f22885,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f22829,f22871])).
% 14.18/2.16  fof(f22829,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f132,f1213,f122])).
% 14.18/2.16  fof(f23391,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0))),
% 14.18/2.16    inference(forward_demodulation,[],[f23390,f4677])).
% 14.18/2.16  fof(f23390,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),sK7(sK0)) = k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0)))),
% 14.18/2.16    inference(forward_demodulation,[],[f22519,f23053])).
% 14.18/2.16  fof(f22519,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k2_lattices(sK0,k3_lattices(sK0,sK8(sK0),sK9(sK0)),sK7(sK0))) = k2_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k3_lattices(sK0,sK8(sK0),sK9(sK0))),sK7(sK0))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f124,f129,f132,f190,f1213,f98])).
% 14.18/2.16  fof(f22828,plain,(
% 14.18/2.16    k2_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f642,f1213,f122])).
% 14.18/2.16  fof(f22878,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))))),
% 14.18/2.16    inference(forward_demodulation,[],[f22842,f22870])).
% 14.18/2.16  fof(f22870,plain,(
% 14.18/2.16    k4_lattices(sK0,k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))),k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f642,f1213,f123])).
% 14.18/2.16  fof(f22842,plain,(
% 14.18/2.16    k2_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0)))) = k4_lattices(sK0,k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))),k3_lattices(sK0,sK9(sK0),k4_lattices(sK0,sK7(sK0),sK8(sK0))))),
% 14.18/2.16    inference(unit_resulting_resolution,[],[f79,f128,f124,f642,f1213,f122])).
% 14.18/2.16  fof(f4809,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) != k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0)))),
% 14.18/2.16    inference(global_subsumption,[],[f81,f79,f4808])).
% 14.18/2.16  fof(f4808,plain,(
% 14.18/2.16    k4_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) != k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 14.18/2.16    inference(forward_demodulation,[],[f4807,f3654])).
% 14.18/2.16  fof(f4807,plain,(
% 14.18/2.16    k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) != k3_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 14.18/2.16    inference(forward_demodulation,[],[f4806,f2784])).
% 14.18/2.16  fof(f4806,plain,(
% 14.18/2.16    k2_lattices(sK0,sK7(sK0),k3_lattices(sK0,sK8(sK0),sK9(sK0))) != k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 14.18/2.16    inference(forward_demodulation,[],[f4805,f2849])).
% 14.18/2.16  fof(f4805,plain,(
% 14.18/2.16    k1_lattices(sK0,k4_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) != k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 14.18/2.16    inference(forward_demodulation,[],[f4804,f3762])).
% 14.18/2.16  fof(f4804,plain,(
% 14.18/2.16    k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0))) != k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),sK8(sK0)),k4_lattices(sK0,sK7(sK0),sK9(sK0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 14.18/2.16    inference(forward_demodulation,[],[f4799,f3774])).
% 14.18/2.16  fof(f4799,plain,(
% 14.18/2.16    k2_lattices(sK0,sK7(sK0),k1_lattices(sK0,sK8(sK0),sK9(sK0))) != k1_lattices(sK0,k2_lattices(sK0,sK7(sK0),sK8(sK0)),k2_lattices(sK0,sK7(sK0),sK9(sK0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 14.18/2.16    inference(resolution,[],[f109,f83])).
% 14.18/2.16  fof(f109,plain,(
% 14.18/2.16    ( ! [X0] : (v11_lattices(X0) | k2_lattices(X0,sK7(X0),k1_lattices(X0,sK8(X0),sK9(X0))) != k1_lattices(X0,k2_lattices(X0,sK7(X0),sK8(X0)),k2_lattices(X0,sK7(X0),sK9(X0))) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 14.18/2.16    inference(cnf_transformation,[],[f68])).
% 14.18/2.16  % SZS output end Proof for theBenchmark
% 14.18/2.16  % (2443)------------------------------
% 14.18/2.16  % (2443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.18/2.16  % (2443)Termination reason: Refutation
% 14.18/2.16  
% 14.18/2.16  % (2443)Memory used [KB]: 38123
% 14.18/2.16  % (2443)Time elapsed: 1.516 s
% 14.18/2.16  % (2443)------------------------------
% 14.18/2.16  % (2443)------------------------------
% 14.35/2.17  % (2420)Success in time 1.804 s
%------------------------------------------------------------------------------
