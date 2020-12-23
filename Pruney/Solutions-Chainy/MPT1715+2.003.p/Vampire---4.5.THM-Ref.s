%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:58 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 828 expanded)
%              Number of leaves         :   13 ( 297 expanded)
%              Depth                    :   29
%              Number of atoms          :  407 (7352 expanded)
%              Number of equality atoms :    6 (  24 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(subsumption_resolution,[],[f178,f39])).

fof(f39,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0) )
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0) )
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0) )
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0) )
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0) )
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0) )
   => ( ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f178,plain,(
    ~ m1_pre_topc(sK1,sK2) ),
    inference(resolution,[],[f177,f162])).

fof(f162,plain,(
    ! [X0] :
      ( r1_tsep_1(X0,sK3)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f161,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f56,f37])).

fof(f37,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f45,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f161,plain,(
    ! [X0] :
      ( r1_tsep_1(X0,sK3)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f160,f101])).

fof(f101,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f96,f37])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X0) ) ),
    inference(subsumption_resolution,[],[f92,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | m1_pre_topc(X0,X0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f91,f35])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,X0)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X0)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f47,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f160,plain,(
    ! [X0] :
      ( r1_tsep_1(X0,sK3)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,sK2)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0] :
      ( r1_tsep_1(X0,sK3)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(sK2,sK2)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(resolution,[],[f156,f118])).

fof(f118,plain,(
    ! [X4,X5] :
      ( r1_tarski(u1_struct_0(X4),u1_struct_0(X5))
      | ~ m1_pre_topc(X5,sK2)
      | ~ m1_pre_topc(X4,sK2)
      | ~ m1_pre_topc(X4,X5) ) ),
    inference(subsumption_resolution,[],[f114,f67])).

fof(f67,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f65,f37])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f64,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f46,f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f114,plain,(
    ! [X4,X5] :
      ( ~ m1_pre_topc(X4,X5)
      | ~ m1_pre_topc(X5,sK2)
      | ~ m1_pre_topc(X4,sK2)
      | r1_tarski(u1_struct_0(X4),u1_struct_0(X5))
      | ~ v2_pre_topc(sK2) ) ),
    inference(resolution,[],[f48,f58])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f156,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | r1_tsep_1(X0,sK3)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f155,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f155,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | r1_tsep_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f154,f59])).

fof(f59,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f56,f38])).

fof(f38,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f154,plain,(
    ! [X0] :
      ( r1_tsep_1(X0,sK3)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | ~ l1_struct_0(X0)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f141,f44])).

fof(f141,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK3)
      | r1_tsep_1(X0,sK3)
      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f137,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f137,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f134,f54])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_struct_0(sK3))
      | ~ r1_tarski(X0,u1_struct_0(sK2))
      | r1_xboole_0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f133,f59])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | r1_xboole_0(X0,X1)
      | ~ l1_pre_topc(sK3) ) ),
    inference(subsumption_resolution,[],[f131,f58])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,u1_struct_0(sK2))
      | ~ r1_tarski(X1,u1_struct_0(sK3))
      | r1_xboole_0(X0,X1)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f130,f82])).

fof(f82,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f81,f58])).

fof(f81,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f80,f59])).

fof(f80,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f77,f44])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f49,f44])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ r1_tarski(X3,u1_struct_0(X2))
      | r1_xboole_0(X0,X3)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f129,f44])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tarski(X2,u1_struct_0(X3))
      | ~ r1_tsep_1(X3,X1)
      | ~ r1_tarski(X0,u1_struct_0(X1))
      | r1_xboole_0(X2,X0)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f89,f44])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X3)
      | ~ r1_tarski(X1,u1_struct_0(X2))
      | ~ r1_tarski(X0,u1_struct_0(X3))
      | ~ r1_tsep_1(X3,X2)
      | ~ l1_struct_0(X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f53,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f177,plain,(
    ~ r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f41,f175])).

fof(f175,plain,(
    r1_tsep_1(sK3,sK1) ),
    inference(resolution,[],[f168,f39])).

fof(f168,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | r1_tsep_1(sK3,X3) ) ),
    inference(subsumption_resolution,[],[f167,f61])).

fof(f167,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | r1_tsep_1(sK3,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(subsumption_resolution,[],[f164,f59])).

fof(f164,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK2)
      | r1_tsep_1(sK3,X3)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(sK3) ) ),
    inference(resolution,[],[f162,f78])).

fof(f41,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:44:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.55  % (3139)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.55  % (3151)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.56  % (3143)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.56  % (3135)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.56  % (3153)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.56  % (3137)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.56  % (3138)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.56  % (3135)Refutation found. Thanks to Tanya!
% 0.23/0.56  % SZS status Theorem for theBenchmark
% 0.23/0.56  % (3137)Refutation not found, incomplete strategy% (3137)------------------------------
% 0.23/0.56  % (3137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (3137)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (3137)Memory used [KB]: 6140
% 0.23/0.56  % (3137)Time elapsed: 0.126 s
% 0.23/0.56  % (3137)------------------------------
% 0.23/0.56  % (3137)------------------------------
% 0.23/0.56  % (3136)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.56  % (3134)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.56  % (3155)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.57  % (3146)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.57  % (3145)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.57  % (3139)Refutation not found, incomplete strategy% (3139)------------------------------
% 0.23/0.57  % (3139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (3139)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (3139)Memory used [KB]: 1663
% 0.23/0.57  % (3139)Time elapsed: 0.127 s
% 0.23/0.57  % (3139)------------------------------
% 0.23/0.57  % (3139)------------------------------
% 0.23/0.57  % (3138)Refutation not found, incomplete strategy% (3138)------------------------------
% 0.23/0.57  % (3138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (3138)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (3138)Memory used [KB]: 10618
% 0.23/0.57  % (3138)Time elapsed: 0.116 s
% 0.23/0.57  % (3138)------------------------------
% 0.23/0.57  % (3138)------------------------------
% 0.23/0.57  % (3145)Refutation not found, incomplete strategy% (3145)------------------------------
% 0.23/0.57  % (3145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (3145)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (3145)Memory used [KB]: 6140
% 0.23/0.57  % (3145)Time elapsed: 0.132 s
% 0.23/0.57  % (3145)------------------------------
% 0.23/0.57  % (3145)------------------------------
% 0.23/0.57  % (3147)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.57  % (3154)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.58  % (3144)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.58  % (3150)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.58  % SZS output start Proof for theBenchmark
% 0.23/0.58  fof(f179,plain,(
% 0.23/0.58    $false),
% 0.23/0.58    inference(subsumption_resolution,[],[f178,f39])).
% 0.23/0.58  fof(f39,plain,(
% 0.23/0.58    m1_pre_topc(sK1,sK2)),
% 0.23/0.58    inference(cnf_transformation,[],[f29])).
% 0.23/0.58  fof(f29,plain,(
% 0.23/0.58    ((((~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.23/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f28,f27,f26,f25])).
% 0.23/0.58  fof(f25,plain,(
% 0.23/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f26,plain,(
% 0.23/0.58    ? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f27,plain,(
% 0.23/0.58    ? [X2] : (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) => (? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(sK2,sK0))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f28,plain,(
% 0.23/0.58    ? [X3] : ((~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) => ((~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0))),
% 0.23/0.58    introduced(choice_axiom,[])).
% 0.23/0.58  fof(f13,plain,(
% 0.23/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.58    inference(flattening,[],[f12])).
% 0.23/0.58  fof(f12,plain,(
% 0.23/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.58    inference(ennf_transformation,[],[f11])).
% 0.23/0.58  fof(f11,plain,(
% 0.23/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.23/0.58    inference(pure_predicate_removal,[],[f10])).
% 0.23/0.58  fof(f10,negated_conjecture,(
% 0.23/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.23/0.58    inference(negated_conjecture,[],[f9])).
% 0.23/0.58  fof(f9,conjecture,(
% 0.23/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 0.23/0.58  fof(f178,plain,(
% 0.23/0.58    ~m1_pre_topc(sK1,sK2)),
% 0.23/0.58    inference(resolution,[],[f177,f162])).
% 0.23/0.58  fof(f162,plain,(
% 0.23/0.58    ( ! [X0] : (r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK2)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f161,f61])).
% 0.23/0.58  fof(f61,plain,(
% 0.23/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 0.23/0.58    inference(resolution,[],[f58,f45])).
% 0.23/0.58  fof(f45,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f16])).
% 0.23/0.58  fof(f16,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.58    inference(ennf_transformation,[],[f5])).
% 0.23/0.58  fof(f5,axiom,(
% 0.23/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.23/0.58  fof(f58,plain,(
% 0.23/0.58    l1_pre_topc(sK2)),
% 0.23/0.58    inference(resolution,[],[f56,f37])).
% 0.23/0.58  fof(f37,plain,(
% 0.23/0.58    m1_pre_topc(sK2,sK0)),
% 0.23/0.58    inference(cnf_transformation,[],[f29])).
% 0.23/0.58  fof(f56,plain,(
% 0.23/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.23/0.58    inference(resolution,[],[f45,f35])).
% 0.23/0.58  fof(f35,plain,(
% 0.23/0.58    l1_pre_topc(sK0)),
% 0.23/0.58    inference(cnf_transformation,[],[f29])).
% 0.23/0.58  fof(f161,plain,(
% 0.23/0.58    ( ! [X0] : (r1_tsep_1(X0,sK3) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,sK2)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f160,f101])).
% 0.23/0.58  fof(f101,plain,(
% 0.23/0.58    m1_pre_topc(sK2,sK2)),
% 0.23/0.58    inference(resolution,[],[f96,f37])).
% 0.23/0.58  fof(f96,plain,(
% 0.23/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X0)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f92,f34])).
% 0.23/0.58  fof(f34,plain,(
% 0.23/0.58    v2_pre_topc(sK0)),
% 0.23/0.58    inference(cnf_transformation,[],[f29])).
% 0.23/0.58  fof(f92,plain,(
% 0.23/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | m1_pre_topc(X0,X0) | ~v2_pre_topc(sK0)) )),
% 0.23/0.58    inference(resolution,[],[f91,f35])).
% 0.23/0.58  fof(f91,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | m1_pre_topc(X0,X0) | ~v2_pre_topc(X1)) )),
% 0.23/0.58    inference(duplicate_literal_removal,[],[f90])).
% 0.23/0.58  fof(f90,plain,(
% 0.23/0.58    ( ! [X0,X1] : (m1_pre_topc(X0,X0) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.23/0.58    inference(resolution,[],[f47,f54])).
% 0.23/0.58  fof(f54,plain,(
% 0.23/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.58    inference(equality_resolution,[],[f51])).
% 0.23/0.58  fof(f51,plain,(
% 0.23/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.58    inference(cnf_transformation,[],[f33])).
% 0.23/0.58  fof(f33,plain,(
% 0.23/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.58    inference(flattening,[],[f32])).
% 0.23/0.58  fof(f32,plain,(
% 0.23/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.58    inference(nnf_transformation,[],[f1])).
% 0.23/0.58  fof(f1,axiom,(
% 0.23/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.58  fof(f47,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f31])).
% 0.23/0.58  fof(f31,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.58    inference(nnf_transformation,[],[f20])).
% 0.23/0.58  fof(f20,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.58    inference(flattening,[],[f19])).
% 0.23/0.58  fof(f19,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.58    inference(ennf_transformation,[],[f8])).
% 0.23/0.58  fof(f8,axiom,(
% 0.23/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.23/0.58  fof(f160,plain,(
% 0.23/0.58    ( ! [X0] : (r1_tsep_1(X0,sK3) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(X0,sK2)) )),
% 0.23/0.58    inference(duplicate_literal_removal,[],[f157])).
% 0.23/0.58  fof(f157,plain,(
% 0.23/0.58    ( ! [X0] : (r1_tsep_1(X0,sK3) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,sK2) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK2)) )),
% 0.23/0.58    inference(resolution,[],[f156,f118])).
% 0.23/0.58  fof(f118,plain,(
% 0.23/0.58    ( ! [X4,X5] : (r1_tarski(u1_struct_0(X4),u1_struct_0(X5)) | ~m1_pre_topc(X5,sK2) | ~m1_pre_topc(X4,sK2) | ~m1_pre_topc(X4,X5)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f114,f67])).
% 0.23/0.58  fof(f67,plain,(
% 0.23/0.58    v2_pre_topc(sK2)),
% 0.23/0.58    inference(resolution,[],[f65,f37])).
% 0.23/0.58  fof(f65,plain,(
% 0.23/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f64,f35])).
% 0.23/0.58  fof(f64,plain,(
% 0.23/0.58    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_pre_topc(X0)) )),
% 0.23/0.58    inference(resolution,[],[f46,f34])).
% 0.23/0.58  fof(f46,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f18])).
% 0.23/0.58  fof(f18,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.58    inference(flattening,[],[f17])).
% 0.23/0.58  fof(f17,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.58    inference(ennf_transformation,[],[f3])).
% 0.23/0.58  fof(f3,axiom,(
% 0.23/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.23/0.58  fof(f114,plain,(
% 0.23/0.58    ( ! [X4,X5] : (~m1_pre_topc(X4,X5) | ~m1_pre_topc(X5,sK2) | ~m1_pre_topc(X4,sK2) | r1_tarski(u1_struct_0(X4),u1_struct_0(X5)) | ~v2_pre_topc(sK2)) )),
% 0.23/0.58    inference(resolution,[],[f48,f58])).
% 0.23/0.58  fof(f48,plain,(
% 0.23/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~v2_pre_topc(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f31])).
% 0.23/0.58  fof(f156,plain,(
% 0.23/0.58    ( ! [X0] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | r1_tsep_1(X0,sK3) | ~l1_pre_topc(X0)) )),
% 0.23/0.58    inference(resolution,[],[f155,f44])).
% 0.23/0.58  fof(f44,plain,(
% 0.23/0.58    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f15])).
% 0.23/0.58  fof(f15,plain,(
% 0.23/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.23/0.58    inference(ennf_transformation,[],[f4])).
% 0.23/0.58  fof(f4,axiom,(
% 0.23/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.23/0.58  fof(f155,plain,(
% 0.23/0.58    ( ! [X0] : (~l1_struct_0(X0) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | r1_tsep_1(X0,sK3)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f154,f59])).
% 0.23/0.58  fof(f59,plain,(
% 0.23/0.58    l1_pre_topc(sK3)),
% 0.23/0.58    inference(resolution,[],[f56,f38])).
% 0.23/0.58  fof(f38,plain,(
% 0.23/0.58    m1_pre_topc(sK3,sK0)),
% 0.23/0.58    inference(cnf_transformation,[],[f29])).
% 0.23/0.58  fof(f154,plain,(
% 0.23/0.58    ( ! [X0] : (r1_tsep_1(X0,sK3) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | ~l1_struct_0(X0) | ~l1_pre_topc(sK3)) )),
% 0.23/0.58    inference(resolution,[],[f141,f44])).
% 0.23/0.58  fof(f141,plain,(
% 0.23/0.58    ( ! [X0] : (~l1_struct_0(sK3) | r1_tsep_1(X0,sK3) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) | ~l1_struct_0(X0)) )),
% 0.23/0.58    inference(resolution,[],[f137,f43])).
% 0.23/0.58  fof(f43,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f30])).
% 0.23/0.58  fof(f30,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.23/0.58    inference(nnf_transformation,[],[f14])).
% 0.23/0.58  fof(f14,plain,(
% 0.23/0.58    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.23/0.58    inference(ennf_transformation,[],[f6])).
% 0.23/0.58  fof(f6,axiom,(
% 0.23/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.23/0.58  fof(f137,plain,(
% 0.23/0.58    ( ! [X0] : (r1_xboole_0(X0,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK2))) )),
% 0.23/0.58    inference(resolution,[],[f134,f54])).
% 0.23/0.58  fof(f134,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~r1_tarski(X1,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK2)) | r1_xboole_0(X0,X1)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f133,f59])).
% 0.23/0.58  fof(f133,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r1_tarski(X1,u1_struct_0(sK3)) | r1_xboole_0(X0,X1) | ~l1_pre_topc(sK3)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f131,f58])).
% 0.23/0.58  fof(f131,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~r1_tarski(X1,u1_struct_0(sK3)) | r1_xboole_0(X0,X1) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK3)) )),
% 0.23/0.58    inference(resolution,[],[f130,f82])).
% 0.23/0.58  fof(f82,plain,(
% 0.23/0.58    r1_tsep_1(sK2,sK3)),
% 0.23/0.58    inference(subsumption_resolution,[],[f81,f58])).
% 0.23/0.58  fof(f81,plain,(
% 0.23/0.58    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK2)),
% 0.23/0.58    inference(subsumption_resolution,[],[f80,f59])).
% 0.23/0.58  fof(f80,plain,(
% 0.23/0.58    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK2)),
% 0.23/0.58    inference(duplicate_literal_removal,[],[f79])).
% 0.23/0.58  fof(f79,plain,(
% 0.23/0.58    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK2) | r1_tsep_1(sK2,sK3)),
% 0.23/0.58    inference(resolution,[],[f78,f40])).
% 0.23/0.58  fof(f40,plain,(
% 0.23/0.58    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.23/0.58    inference(cnf_transformation,[],[f29])).
% 0.23/0.58  fof(f78,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 0.23/0.58    inference(resolution,[],[f77,f44])).
% 0.23/0.58  fof(f77,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.58    inference(resolution,[],[f49,f44])).
% 0.23/0.58  fof(f49,plain,(
% 0.23/0.58    ( ! [X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_tsep_1(X1,X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f22])).
% 0.23/0.58  fof(f22,plain,(
% 0.23/0.58    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.23/0.58    inference(flattening,[],[f21])).
% 0.23/0.58  fof(f21,plain,(
% 0.23/0.58    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.23/0.58    inference(ennf_transformation,[],[f7])).
% 0.23/0.58  fof(f7,axiom,(
% 0.23/0.58    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.23/0.58  fof(f130,plain,(
% 0.23/0.58    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X1,X2) | ~r1_tarski(X0,u1_struct_0(X1)) | ~r1_tarski(X3,u1_struct_0(X2)) | r1_xboole_0(X0,X3) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2)) )),
% 0.23/0.58    inference(resolution,[],[f129,f44])).
% 0.23/0.58  fof(f129,plain,(
% 0.23/0.58    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X1) | ~r1_tarski(X2,u1_struct_0(X3)) | ~r1_tsep_1(X3,X1) | ~r1_tarski(X0,u1_struct_0(X1)) | r1_xboole_0(X2,X0) | ~l1_pre_topc(X3)) )),
% 0.23/0.58    inference(resolution,[],[f89,f44])).
% 0.23/0.58  fof(f89,plain,(
% 0.23/0.58    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X3) | ~r1_tarski(X1,u1_struct_0(X2)) | ~r1_tarski(X0,u1_struct_0(X3)) | ~r1_tsep_1(X3,X2) | ~l1_struct_0(X2) | r1_xboole_0(X0,X1)) )),
% 0.23/0.58    inference(resolution,[],[f53,f42])).
% 0.23/0.58  fof(f42,plain,(
% 0.23/0.58    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f30])).
% 0.23/0.58  fof(f53,plain,(
% 0.23/0.58    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X1,X3) | r1_xboole_0(X0,X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.23/0.58    inference(cnf_transformation,[],[f24])).
% 0.23/0.58  fof(f24,plain,(
% 0.23/0.58    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.23/0.58    inference(flattening,[],[f23])).
% 0.23/0.58  fof(f23,plain,(
% 0.23/0.58    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.23/0.58    inference(ennf_transformation,[],[f2])).
% 0.23/0.58  fof(f2,axiom,(
% 0.23/0.58    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.23/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.23/0.58  fof(f177,plain,(
% 0.23/0.58    ~r1_tsep_1(sK1,sK3)),
% 0.23/0.58    inference(subsumption_resolution,[],[f41,f175])).
% 0.23/0.58  fof(f175,plain,(
% 0.23/0.58    r1_tsep_1(sK3,sK1)),
% 0.23/0.58    inference(resolution,[],[f168,f39])).
% 0.23/0.58  fof(f168,plain,(
% 0.23/0.58    ( ! [X3] : (~m1_pre_topc(X3,sK2) | r1_tsep_1(sK3,X3)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f167,f61])).
% 0.23/0.58  fof(f167,plain,(
% 0.23/0.58    ( ! [X3] : (~m1_pre_topc(X3,sK2) | r1_tsep_1(sK3,X3) | ~l1_pre_topc(X3)) )),
% 0.23/0.58    inference(subsumption_resolution,[],[f164,f59])).
% 0.23/0.58  fof(f164,plain,(
% 0.23/0.58    ( ! [X3] : (~m1_pre_topc(X3,sK2) | r1_tsep_1(sK3,X3) | ~l1_pre_topc(X3) | ~l1_pre_topc(sK3)) )),
% 0.23/0.58    inference(resolution,[],[f162,f78])).
% 0.23/0.58  fof(f41,plain,(
% 0.23/0.58    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.23/0.58    inference(cnf_transformation,[],[f29])).
% 0.23/0.58  % SZS output end Proof for theBenchmark
% 0.23/0.58  % (3135)------------------------------
% 0.23/0.58  % (3135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (3135)Termination reason: Refutation
% 0.23/0.58  
% 0.23/0.58  % (3135)Memory used [KB]: 6268
% 0.23/0.58  % (3135)Time elapsed: 0.128 s
% 0.23/0.58  % (3135)------------------------------
% 0.23/0.58  % (3135)------------------------------
% 0.23/0.58  % (3152)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.58  % (3131)Success in time 0.211 s
%------------------------------------------------------------------------------
