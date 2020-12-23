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
% DateTime   : Thu Dec  3 13:22:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 407 expanded)
%              Number of leaves         :   24 ( 118 expanded)
%              Depth                    :   21
%              Number of atoms          :  441 (1855 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f327,plain,(
    $false ),
    inference(resolution,[],[f325,f320])).

fof(f320,plain,(
    ! [X2,X3] : ~ r2_hidden(sK9(k6_subset_1(X2,X3)),X3) ),
    inference(subsumption_resolution,[],[f226,f290])).

fof(f290,plain,(
    ! [X0] : ~ v1_xboole_0(X0) ),
    inference(resolution,[],[f282,f108])).

fof(f108,plain,(
    ! [X0] :
      ( sP13(sK10(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f101,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f5,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f101,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP13(X1) ) ),
    inference(cnf_transformation,[],[f101_D])).

fof(f101_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP13(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP13])])).

fof(f282,plain,(
    ! [X0] : ~ sP13(X0) ),
    inference(resolution,[],[f255,f79])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ sP13(X0) ) ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ sP13(X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ sP13(X0) ) ),
    inference(resolution,[],[f224,f146])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X3,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ sP13(X0) ) ),
    inference(resolution,[],[f144,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X2,X1,X0,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ sP0(X2,X1,X0,sK7(X0,X1,X2))
          & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X1,X0,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP0(X2,X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ sP0(X2,X1,X0,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ sP0(X2,X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X1,X0,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ sP0(X2,X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( sP0(X2,X1,X0,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( sP0(X2,X1,X0,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ sP13(X0) ) ),
    inference(resolution,[],[f75,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP13(X1) ) ),
    inference(general_splitting,[],[f95,f101_D])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k2_waybel_0(X2,X1,sK8(X0,X1,X2,X3)),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
            | ~ r1_orders_2(X1,X3,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ( r2_hidden(k2_waybel_0(X2,X1,sK8(X0,X1,X2,X3)),X0)
          & r1_orders_2(X1,X3,sK8(X0,X1,X2,X3))
          & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f43,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(k2_waybel_0(X2,X1,X5),X0)
          & r1_orders_2(X1,X3,X5)
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X2,X1,sK8(X0,X1,X2,X3)),X0)
        & r1_orders_2(X1,X3,sK8(X0,X1,X2,X3))
        & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
            | ~ r1_orders_2(X1,X3,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ? [X5] :
            ( r2_hidden(k2_waybel_0(X2,X1,X5),X0)
            & r1_orders_2(X1,X3,X5)
            & m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,X3,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            & r1_orders_2(X1,X3,X4)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ? [X4] :
          ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f224,plain,(
    ! [X0] :
      ( sP1(sK5,sK6,X0)
      | ~ sP13(X0) ) ),
    inference(subsumption_resolution,[],[f223,f138])).

fof(f138,plain,(
    sP2(sK6,sK5) ),
    inference(subsumption_resolution,[],[f137,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5))
    & l1_waybel_0(sK6,sK5)
    & ~ v2_struct_0(sK6)
    & l1_struct_0(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK5,X1,u1_struct_0(sK5))
          & l1_waybel_0(X1,sK5)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK5,X1,u1_struct_0(sK5))
        & l1_waybel_0(X1,sK5)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5))
      & l1_waybel_0(sK6,sK5)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f137,plain,
    ( sP2(sK6,sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f136,f62])).

fof(f62,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f136,plain,
    ( sP2(sK6,sK5)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f135,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f135,plain,
    ( sP2(sK6,sK5)
    | v2_struct_0(sK6)
    | ~ l1_struct_0(sK5)
    | v2_struct_0(sK5) ),
    inference(resolution,[],[f77,f64])).

fof(f64,plain,(
    l1_waybel_0(sK6,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | sP2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f27,f26,f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( r2_waybel_0(X0,X1,X2)
        <=> sP1(X0,X1,X2) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f223,plain,(
    ! [X0] :
      ( ~ sP13(X0)
      | sP1(sK5,sK6,X0)
      | ~ sP2(sK6,sK5) ) ),
    inference(resolution,[],[f221,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X1,X0,X2)
      | sP1(X1,X0,X2)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_waybel_0(X1,X0,X2)
            | ~ sP1(X1,X0,X2) )
          & ( sP1(X1,X0,X2)
            | ~ r2_waybel_0(X1,X0,X2) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( r2_waybel_0(X0,X1,X2)
            | ~ sP1(X0,X1,X2) )
          & ( sP1(X0,X1,X2)
            | ~ r2_waybel_0(X0,X1,X2) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f221,plain,(
    ! [X0] :
      ( r2_waybel_0(sK5,sK6,X0)
      | ~ sP13(X0) ) ),
    inference(resolution,[],[f209,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ sP13(X1) ) ),
    inference(resolution,[],[f82,f102])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f23,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f209,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(u1_struct_0(sK5),X0)
      | r2_waybel_0(sK5,sK6,X0) ) ),
    inference(subsumption_resolution,[],[f208,f61])).

fof(f208,plain,(
    ! [X0] :
      ( r2_waybel_0(sK5,sK6,X0)
      | v2_struct_0(sK5)
      | ~ r1_xboole_0(u1_struct_0(sK5),X0) ) ),
    inference(subsumption_resolution,[],[f207,f62])).

fof(f207,plain,(
    ! [X0] :
      ( r2_waybel_0(sK5,sK6,X0)
      | ~ l1_struct_0(sK5)
      | v2_struct_0(sK5)
      | ~ r1_xboole_0(u1_struct_0(sK5),X0) ) ),
    inference(subsumption_resolution,[],[f206,f63])).

fof(f206,plain,(
    ! [X0] :
      ( r2_waybel_0(sK5,sK6,X0)
      | v2_struct_0(sK6)
      | ~ l1_struct_0(sK5)
      | v2_struct_0(sK5)
      | ~ r1_xboole_0(u1_struct_0(sK5),X0) ) ),
    inference(subsumption_resolution,[],[f203,f64])).

fof(f203,plain,(
    ! [X0] :
      ( r2_waybel_0(sK5,sK6,X0)
      | ~ l1_waybel_0(sK6,sK5)
      | v2_struct_0(sK6)
      | ~ l1_struct_0(sK5)
      | v2_struct_0(sK5)
      | ~ r1_xboole_0(u1_struct_0(sK5),X0) ) ),
    inference(resolution,[],[f162,f65])).

fof(f65,plain,(
    ~ r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f162,plain,(
    ! [X6,X4,X5] :
      ( r1_waybel_0(X4,X6,u1_struct_0(X4))
      | r2_waybel_0(X4,X6,X5)
      | ~ l1_waybel_0(X6,X4)
      | v2_struct_0(X6)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4)
      | ~ r1_xboole_0(u1_struct_0(X4),X5) ) ),
    inference(superposition,[],[f67,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f84,f80])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f226,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k6_subset_1(X2,X3))
      | ~ r2_hidden(sK9(k6_subset_1(X2,X3)),X3) ) ),
    inference(resolution,[],[f124,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X1,X3,X0] :
      ( ( sP3(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP3(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X3,X0] :
      ( sP3(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f124,plain,(
    ! [X0,X1] :
      ( sP3(X0,sK9(k6_subset_1(X1,X0)),X1)
      | v1_xboole_0(k6_subset_1(X1,X0)) ) ),
    inference(resolution,[],[f122,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK9(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f22,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k6_subset_1(X1,X2))
      | sP3(X2,X0,X1) ) ),
    inference(resolution,[],[f86,f100])).

fof(f100,plain,(
    ! [X0,X1] : sP4(X0,X1,k6_subset_1(X0,X1)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f93,f80])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP4(X0,X1,X2) )
      & ( sP4(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP4(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f30,f29])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP3(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP3(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ( ~ sP3(X1,sK12(X0,X1,X2),X0)
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( sP3(X1,sK12(X0,X1,X2),X0)
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP3(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP3(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP3(X1,sK12(X0,X1,X2),X0)
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( sP3(X1,sK12(X0,X1,X2),X0)
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP3(X1,X4,X0) )
            & ( sP3(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP3(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP3(X1,X3,X0) )
            & ( sP3(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f325,plain,(
    ! [X4,X5] : r2_hidden(sK9(k6_subset_1(X4,X5)),X4) ),
    inference(subsumption_resolution,[],[f227,f290])).

fof(f227,plain,(
    ! [X4,X5] :
      ( v1_xboole_0(k6_subset_1(X4,X5))
      | r2_hidden(sK9(k6_subset_1(X4,X5)),X4) ) ),
    inference(resolution,[],[f124,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:17:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (4358)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (4350)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (4345)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (4344)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (4344)Refutation not found, incomplete strategy% (4344)------------------------------
% 0.22/0.54  % (4344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4344)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4344)Memory used [KB]: 10746
% 0.22/0.54  % (4344)Time elapsed: 0.121 s
% 0.22/0.54  % (4344)------------------------------
% 0.22/0.54  % (4344)------------------------------
% 0.22/0.54  % (4342)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (4343)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (4357)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (4370)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (4365)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (4346)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (4356)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (4346)Refutation not found, incomplete strategy% (4346)------------------------------
% 0.22/0.55  % (4346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4346)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4346)Memory used [KB]: 6268
% 0.22/0.55  % (4346)Time elapsed: 0.124 s
% 0.22/0.55  % (4346)------------------------------
% 0.22/0.55  % (4346)------------------------------
% 0.22/0.55  % (4372)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (4347)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (4351)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (4351)Refutation not found, incomplete strategy% (4351)------------------------------
% 0.22/0.55  % (4351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4351)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4351)Memory used [KB]: 10618
% 0.22/0.55  % (4351)Time elapsed: 0.133 s
% 0.22/0.55  % (4351)------------------------------
% 0.22/0.55  % (4351)------------------------------
% 0.22/0.55  % (4366)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (4355)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (4353)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (4354)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (4362)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (4354)Refutation not found, incomplete strategy% (4354)------------------------------
% 0.22/0.55  % (4354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4354)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4354)Memory used [KB]: 10618
% 0.22/0.55  % (4354)Time elapsed: 0.137 s
% 0.22/0.55  % (4354)------------------------------
% 0.22/0.55  % (4354)------------------------------
% 0.22/0.55  % (4348)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (4371)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (4367)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (4364)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (4361)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (4364)Refutation not found, incomplete strategy% (4364)------------------------------
% 0.22/0.56  % (4364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4364)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4364)Memory used [KB]: 1663
% 0.22/0.56  % (4364)Time elapsed: 0.148 s
% 0.22/0.56  % (4364)------------------------------
% 0.22/0.56  % (4364)------------------------------
% 0.22/0.56  % (4363)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (4369)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (4363)Refutation not found, incomplete strategy% (4363)------------------------------
% 0.22/0.56  % (4363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4363)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4363)Memory used [KB]: 10746
% 0.22/0.56  % (4363)Time elapsed: 0.150 s
% 0.22/0.56  % (4363)------------------------------
% 0.22/0.56  % (4363)------------------------------
% 0.22/0.56  % (4353)Refutation not found, incomplete strategy% (4353)------------------------------
% 0.22/0.56  % (4353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4353)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4353)Memory used [KB]: 10618
% 0.22/0.56  % (4353)Time elapsed: 0.146 s
% 0.22/0.56  % (4353)------------------------------
% 0.22/0.56  % (4353)------------------------------
% 0.22/0.56  % (4369)Refutation not found, incomplete strategy% (4369)------------------------------
% 0.22/0.56  % (4369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (4369)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (4369)Memory used [KB]: 10746
% 0.22/0.56  % (4369)Time elapsed: 0.146 s
% 0.22/0.56  % (4369)------------------------------
% 0.22/0.56  % (4369)------------------------------
% 0.22/0.57  % (4365)Refutation not found, incomplete strategy% (4365)------------------------------
% 0.22/0.57  % (4365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (4365)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (4365)Memory used [KB]: 10746
% 0.22/0.57  % (4365)Time elapsed: 0.095 s
% 0.22/0.57  % (4365)------------------------------
% 0.22/0.57  % (4365)------------------------------
% 0.22/0.57  % (4372)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f327,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(resolution,[],[f325,f320])).
% 0.22/0.57  fof(f320,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~r2_hidden(sK9(k6_subset_1(X2,X3)),X3)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f226,f290])).
% 0.22/0.57  fof(f290,plain,(
% 0.22/0.57    ( ! [X0] : (~v1_xboole_0(X0)) )),
% 0.22/0.57    inference(resolution,[],[f282,f108])).
% 0.22/0.57  fof(f108,plain,(
% 0.22/0.57    ( ! [X0] : (sP13(sK10(k1_zfmisc_1(X0))) | ~v1_xboole_0(X0)) )),
% 0.22/0.57    inference(resolution,[],[f101,f79])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X0] : (m1_subset_1(sK10(X0),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ! [X0] : m1_subset_1(sK10(X0),X0)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f5,f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK10(X0),X0))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.57  fof(f101,plain,(
% 0.22/0.57    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP13(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f101_D])).
% 0.22/0.57  fof(f101_D,plain,(
% 0.22/0.57    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP13(X1)) )),
% 0.22/0.57    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP13])])).
% 0.22/0.57  fof(f282,plain,(
% 0.22/0.57    ( ! [X0] : (~sP13(X0)) )),
% 0.22/0.57    inference(resolution,[],[f255,f79])).
% 0.22/0.57  fof(f255,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK6)) | ~sP13(X0)) )),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f253])).
% 0.22/0.57  fof(f253,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~sP13(X0) | ~m1_subset_1(X1,u1_struct_0(sK6)) | ~sP13(X0)) )),
% 0.22/0.57    inference(resolution,[],[f224,f146])).
% 0.22/0.57  fof(f146,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~sP1(X3,X2,X0) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~sP13(X0)) )),
% 0.22/0.57    inference(resolution,[],[f144,f70])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (sP0(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP1(X0,X1,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~sP0(X2,X1,X0,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (sP0(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : (~sP0(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~sP0(X2,X1,X0,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~sP0(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (sP0(X2,X1,X0,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.22/0.57    inference(rectify,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~sP0(X2,X1,X0,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (sP0(X2,X1,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.22/0.57    inference(nnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (sP0(X2,X1,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X1))))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.57  fof(f144,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | ~sP13(X0)) )),
% 0.22/0.57    inference(resolution,[],[f75,f102])).
% 0.22/0.57  fof(f102,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP13(X1)) )),
% 0.22/0.57    inference(general_splitting,[],[f95,f101_D])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(k2_waybel_0(X2,X1,sK8(X0,X1,X2,X3)),X0) | ~sP0(X0,X1,X2,X3)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)))) & ((r2_hidden(k2_waybel_0(X2,X1,sK8(X0,X1,X2,X3)),X0) & r1_orders_2(X1,X3,sK8(X0,X1,X2,X3)) & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f43,f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ! [X3,X2,X1,X0] : (? [X5] : (r2_hidden(k2_waybel_0(X2,X1,X5),X0) & r1_orders_2(X1,X3,X5) & m1_subset_1(X5,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X2,X1,sK8(X0,X1,X2,X3)),X0) & r1_orders_2(X1,X3,sK8(X0,X1,X2,X3)) & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ! [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X5] : (r2_hidden(k2_waybel_0(X2,X1,X5),X0) & r1_orders_2(X1,X3,X5) & m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.57    inference(rectify,[],[f42])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X2,X1,X0,X3)))),
% 0.22/0.57    inference(nnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.57  fof(f224,plain,(
% 0.22/0.57    ( ! [X0] : (sP1(sK5,sK6,X0) | ~sP13(X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f223,f138])).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    sP2(sK6,sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f137,f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ~v2_struct_0(sK5)),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    (~r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) & l1_waybel_0(sK6,sK5) & ~v2_struct_0(sK6)) & l1_struct_0(sK5) & ~v2_struct_0(sK5)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f17,f33,f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK5,X1,u1_struct_0(sK5)) & l1_waybel_0(X1,sK5) & ~v2_struct_0(X1)) & l1_struct_0(sK5) & ~v2_struct_0(sK5))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ? [X1] : (~r1_waybel_0(sK5,X1,u1_struct_0(sK5)) & l1_waybel_0(X1,sK5) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK5,sK6,u1_struct_0(sK5)) & l1_waybel_0(sK6,sK5) & ~v2_struct_0(sK6))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.57    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.57    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.57  fof(f11,negated_conjecture,(
% 0.22/0.57    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.57    inference(negated_conjecture,[],[f10])).
% 0.22/0.57  fof(f10,conjecture,(
% 0.22/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    sP2(sK6,sK5) | v2_struct_0(sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f136,f62])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    l1_struct_0(sK5)),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f136,plain,(
% 0.22/0.57    sP2(sK6,sK5) | ~l1_struct_0(sK5) | v2_struct_0(sK5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f135,f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ~v2_struct_0(sK6)),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f135,plain,(
% 0.22/0.57    sP2(sK6,sK5) | v2_struct_0(sK6) | ~l1_struct_0(sK5) | v2_struct_0(sK5)),
% 0.22/0.57    inference(resolution,[],[f77,f64])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    l1_waybel_0(sK6,sK5)),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | sP2(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (sP2(X1,X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(definition_folding,[],[f21,f27,f26,f25])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X1,X0] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> sP1(X0,X1,X2)) | ~sP2(X1,X0))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.22/0.57  fof(f223,plain,(
% 0.22/0.57    ( ! [X0] : (~sP13(X0) | sP1(sK5,sK6,X0) | ~sP2(sK6,sK5)) )),
% 0.22/0.57    inference(resolution,[],[f221,f68])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_waybel_0(X1,X0,X2) | sP1(X1,X0,X2) | ~sP2(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : ((r2_waybel_0(X1,X0,X2) | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | ~r2_waybel_0(X1,X0,X2))) | ~sP2(X0,X1))),
% 0.22/0.57    inference(rectify,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X1,X0] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | ~r2_waybel_0(X0,X1,X2))) | ~sP2(X1,X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f27])).
% 0.22/0.57  fof(f221,plain,(
% 0.22/0.57    ( ! [X0] : (r2_waybel_0(sK5,sK6,X0) | ~sP13(X0)) )),
% 0.22/0.57    inference(resolution,[],[f209,f105])).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~sP13(X1)) )),
% 0.22/0.57    inference(resolution,[],[f82,f102])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f23,f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.57  fof(f209,plain,(
% 0.22/0.57    ( ! [X0] : (~r1_xboole_0(u1_struct_0(sK5),X0) | r2_waybel_0(sK5,sK6,X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f208,f61])).
% 0.22/0.57  fof(f208,plain,(
% 0.22/0.57    ( ! [X0] : (r2_waybel_0(sK5,sK6,X0) | v2_struct_0(sK5) | ~r1_xboole_0(u1_struct_0(sK5),X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f207,f62])).
% 0.22/0.57  fof(f207,plain,(
% 0.22/0.57    ( ! [X0] : (r2_waybel_0(sK5,sK6,X0) | ~l1_struct_0(sK5) | v2_struct_0(sK5) | ~r1_xboole_0(u1_struct_0(sK5),X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f206,f63])).
% 0.22/0.57  fof(f206,plain,(
% 0.22/0.57    ( ! [X0] : (r2_waybel_0(sK5,sK6,X0) | v2_struct_0(sK6) | ~l1_struct_0(sK5) | v2_struct_0(sK5) | ~r1_xboole_0(u1_struct_0(sK5),X0)) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f203,f64])).
% 0.22/0.57  fof(f203,plain,(
% 0.22/0.57    ( ! [X0] : (r2_waybel_0(sK5,sK6,X0) | ~l1_waybel_0(sK6,sK5) | v2_struct_0(sK6) | ~l1_struct_0(sK5) | v2_struct_0(sK5) | ~r1_xboole_0(u1_struct_0(sK5),X0)) )),
% 0.22/0.57    inference(resolution,[],[f162,f65])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    ~r1_waybel_0(sK5,sK6,u1_struct_0(sK5))),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f162,plain,(
% 0.22/0.57    ( ! [X6,X4,X5] : (r1_waybel_0(X4,X6,u1_struct_0(X4)) | r2_waybel_0(X4,X6,X5) | ~l1_waybel_0(X6,X4) | v2_struct_0(X6) | ~l1_struct_0(X4) | v2_struct_0(X4) | ~r1_xboole_0(u1_struct_0(X4),X5)) )),
% 0.22/0.57    inference(superposition,[],[f67,f97])).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k6_subset_1(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f84,f80])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.22/0.57  fof(f226,plain,(
% 0.22/0.57    ( ! [X2,X3] : (v1_xboole_0(k6_subset_1(X2,X3)) | ~r2_hidden(sK9(k6_subset_1(X2,X3)),X3)) )),
% 0.22/0.57    inference(resolution,[],[f124,f91])).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP3(X0,X1,X2)))),
% 0.22/0.57    inference(rectify,[],[f58])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP3(X1,X3,X0)))),
% 0.22/0.57    inference(flattening,[],[f57])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    ! [X1,X3,X0] : ((sP3(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP3(X1,X3,X0)))),
% 0.22/0.57    inference(nnf_transformation,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X1,X3,X0] : (sP3(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.57  fof(f124,plain,(
% 0.22/0.57    ( ! [X0,X1] : (sP3(X0,sK9(k6_subset_1(X1,X0)),X1) | v1_xboole_0(k6_subset_1(X1,X0))) )),
% 0.22/0.57    inference(resolution,[],[f122,f78])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK9(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK9(X0),X0))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f22,f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.22/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.57  fof(f122,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k6_subset_1(X1,X2)) | sP3(X2,X0,X1)) )),
% 0.22/0.57    inference(resolution,[],[f86,f100])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    ( ! [X0,X1] : (sP4(X0,X1,k6_subset_1(X0,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f99])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | k6_subset_1(X0,X1) != X2) )),
% 0.22/0.57    inference(definition_unfolding,[],[f93,f80])).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP4(X0,X1,X2)) & (sP4(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP4(X0,X1,X2))),
% 0.22/0.57    inference(definition_folding,[],[f2,f30,f29])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (sP4(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP3(X1,X3,X0)))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (~sP4(X0,X1,X2) | ~r2_hidden(X4,X2) | sP3(X1,X4,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ((~sP3(X1,sK12(X0,X1,X2),X0) | ~r2_hidden(sK12(X0,X1,X2),X2)) & (sP3(X1,sK12(X0,X1,X2),X0) | r2_hidden(sK12(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP3(X1,X4,X0)) & (sP3(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f54,f55])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP3(X1,sK12(X0,X1,X2),X0) | ~r2_hidden(sK12(X0,X1,X2),X2)) & (sP3(X1,sK12(X0,X1,X2),X0) | r2_hidden(sK12(X0,X1,X2),X2))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP3(X1,X4,X0)) & (sP3(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP4(X0,X1,X2)))),
% 0.22/0.58    inference(rectify,[],[f53])).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : ((~sP3(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP3(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP3(X1,X3,X0)) & (sP3(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP4(X0,X1,X2)))),
% 0.22/0.58    inference(nnf_transformation,[],[f30])).
% 0.22/0.58  fof(f325,plain,(
% 0.22/0.58    ( ! [X4,X5] : (r2_hidden(sK9(k6_subset_1(X4,X5)),X4)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f227,f290])).
% 0.22/0.58  fof(f227,plain,(
% 0.22/0.58    ( ! [X4,X5] : (v1_xboole_0(k6_subset_1(X4,X5)) | r2_hidden(sK9(k6_subset_1(X4,X5)),X4)) )),
% 0.22/0.58    inference(resolution,[],[f124,f90])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f59])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (4372)------------------------------
% 0.22/0.58  % (4372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (4372)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (4372)Memory used [KB]: 1918
% 0.22/0.58  % (4372)Time elapsed: 0.154 s
% 0.22/0.58  % (4372)------------------------------
% 0.22/0.58  % (4372)------------------------------
% 0.22/0.58  % (4340)Success in time 0.207 s
%------------------------------------------------------------------------------
